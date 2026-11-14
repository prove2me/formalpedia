-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.suppressed_stopping_coin_zero_random_state
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:15:59.96469+00:00
-- url     : https://prove2.me/submissions/6245e1cc-1420-489f-9d87-91c39b68173d

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
import Theorems.Thm_CountingLLL_ReciprocalTest_entropyCode_law
import Theorems.Thm_CountingLLL_ReciprocalTest_encoded_read_marginals
import Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_reveal_fresh_simulation
import Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_history_fresh
import Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_stopping_coin_zero
import Theorems.Thm_CountingLLL_RevealMachine_history_fresh_query
import Theorems.Thm_CountingLLL_RevealMachine_run_depends_on_seen
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest CountingLLL.RevealMachine
open scoped ENNReal

deriving instance Encodable for Context
deriving instance Encodable for Phase
deriving instance Encodable for State

private theorem finite_dep_meas (S : Finset ReadIndex) (E : Set (ReadIndex → ℕ))
    (hE : ∀ ω ω', (∀ i ∈ S, ω i = ω' i) → (ω ∈ E ↔ ω' ∈ E)) : MeasurableSet E := by
  classical
  let f : (ReadIndex → ℕ) → (S → ℕ) := fun ω j => ω j
  have hf : Measurable f := measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
  let F : Set (S → ℕ) := {x | ∃ ω : ReadIndex → ℕ, f ω = x ∧ ω ∈ E}
  have heq : f ⁻¹' F = E := by
    ext ω
    constructor
    · rintro ⟨ω', heq, hn⟩
      apply (hE ω ω' ?_).2 hn
      intro i hi
      exact (congrFun heq ⟨i,hi⟩).symm
    · intro hn; exact ⟨ω, rfl, hn⟩
  rw [← heq]
  exact (Set.to_countable F).measurableSet.preimage hf

private theorem state_event_meas (n : ℕ) (s : State) :
    MeasurableSet {x : ReadIndex → ℕ | (CountingLLL.RevealMachine.run suppressedRevealProgram x initial n).1 = s} := by
  let C : Finset ReadIndex → Set (ReadIndex → ℕ) := fun S =>
    {x | (CountingLLL.RevealMachine.run suppressedRevealProgram x initial n).1 = s ∧
      (CountingLLL.RevealMachine.run suppressedRevealProgram x initial n).2 = S}
  have hc (S : Finset ReadIndex) : MeasurableSet (C S) := by
    apply finite_dep_meas S (C S)
    intro x y h
    constructor
    · rintro ⟨hstate,hseen⟩
      have heq := run_depends_on_seen suppressedRevealProgram x y initial n (by simpa [hseen] using h)
      exact ⟨by simpa [← heq] using hstate, by simpa [← heq] using hseen⟩
    · rintro ⟨hstate,hseen⟩
      have heq := run_depends_on_seen suppressedRevealProgram y x initial n (by
        intro i hi; exact (h i (by simpa [hseen] using hi)).symm)
      exact ⟨by simpa [← heq] using hstate, by simpa [← heq] using hseen⟩
  have heq : {x : ReadIndex → ℕ | (CountingLLL.RevealMachine.run suppressedRevealProgram x initial n).1 = s} = ⋃ S, C S := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hs; exact ⟨(CountingLLL.RevealMachine.run suppressedRevealProgram x initial n).2, hs, rfl⟩
    · rintro ⟨S,hs,hS⟩; exact hs
  rw [heq]
  exact MeasurableSet.iUnion hc

private theorem code_meas : Measurable entropyCode := by
  apply measurable_pi_lambda
  intro a
  cases a with
  | inl i =>
    change Measurable (fun ω : Entropy => if ω.1 i then (1:ℕ) else 0)
    exact (measurable_of_countable bitCode).comp ((measurable_pi_apply i).comp measurable_fst)
  | inr a =>
    cases a with
    | inl i =>
      change Measurable (fun ω : Entropy => if ω.2.1 i then (1:ℕ) else 0)
      exact (measurable_of_countable bitCode).comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
    | inr a =>
      change Measurable (fun ω : Entropy => (ω.2.2 a).val)
      exact (measurable_of_countable (fun x : Fin (a.1+1) => x.val)).comp
        ((measurable_pi_apply a).comp (measurable_snd.comp measurable_snd))


private theorem history_event_meas (n : ℕ) (H : (Fin (n+1) → State) → Prop) :
    MeasurableSet {x : ReadIndex → ℕ | H (fun j => (CountingLLL.RevealMachine.run suppressedRevealProgram x initial j.val).1)} := by
  classical
  let C : (Fin (n+1) → State) → Set (ReadIndex → ℕ) := fun f =>
    if H f then ⋂ j : Fin (n+1), {x | (CountingLLL.RevealMachine.run suppressedRevealProgram x initial j.val).1 = f j} else ∅
  have hc (f : Fin (n+1) → State) : MeasurableSet (C f) := by
    by_cases hf : H f
    · simp only [C, if_pos hf]
      exact MeasurableSet.iInter (fun j => state_event_meas j.val (f j))
    · simp [C, hf]
  have heq : {x : ReadIndex → ℕ | H (fun j => (CountingLLL.RevealMachine.run suppressedRevealProgram x initial j.val).1)} = ⋃ f, C f := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, C]
    constructor
    · intro hx
      refine ⟨(fun j => (CountingLLL.RevealMachine.run suppressedRevealProgram x initial j.val).1), ?_⟩
      simp [hx]
    · rintro ⟨f, hf⟩
      by_cases hH : H f
      · simp only [if_pos hH, Set.mem_iInter, Set.mem_setOf_eq] at hf
        have : (fun j : Fin (n+1) => (CountingLLL.RevealMachine.run suppressedRevealProgram x initial j.val).1) = f := funext hf
        simpa [this] using hH
      · simp [hH] at hf
  rw [heq]
  exact MeasurableSet.iUnion hc


private theorem operational_history_meas (n : ℕ) (H : (Fin (n+1) → State) → Prop) :
    MeasurableSet {ω : Entropy | H (fun j => allSuppressedRun ω j.val)} := by
  have h := (history_event_meas n H).preimage code_meas
  have he : entropyCode ⁻¹' {x | H (fun j => (CountingLLL.RevealMachine.run suppressedRevealProgram x initial j.val).1)} =
      {ω | H (fun j => allSuppressedRun ω j.val)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, suppressed_reveal_fresh_simulation.1]
  simpa only [he] using h



/-- The B/2 two-step Coin-zero law with a random current state. -/
theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) (T : Entropy → Option ℕ)
    (H : (n : ℕ) → (Fin (n+1) → State) → Prop)
    (hT : ∀ ω n, T ω = some n ↔ H n (fun j => allSuppressedRun ω j.val)) (k : Context) :
    entropyLaw B {ω | ∃ n, T ω = some n ∧ (allSuppressedRun ω n).phase = .coinOracle k ∧
      let s := allSuppressedRun ω n
      let u : State := {s with oracleUsed := s.oracleUsed+1, phase := .coinFair k}
      let v : State := coinReturn k false {u with fairUsed := u.fairUsed+1}
      allSuppressedRun ω (n+1) = u ∧ allSuppressedRun ω (n+2) = v} =
    entropyLaw B {ω | ∃ n, T ω = some n ∧ (allSuppressedRun ω n).phase = .coinOracle k} * (B/2) := by
  classical
  let E : State → Set Entropy := fun s => {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s ∧ s.phase = .coinOracle k}
  let F : State → Set Entropy := fun s => {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s ∧ s.phase = .coinOracle k ∧
    allSuppressedRun ω (n+1) = {s with oracleUsed := s.oracleUsed+1, phase := .coinFair k} ∧
    allSuppressedRun ω (n+2) = coinReturn k false {{s with oracleUsed := s.oracleUsed+1, phase := .coinFair k} with fairUsed := s.fairUsed+1}}
  have hE (s : State) : MeasurableSet (E s) := by
    by_cases hs : s.phase = .coinOracle k
    · have he : E s = ⋃ n, {ω | T ω = some n ∧ allSuppressedRun ω n = s} := by ext ω; simp [E,hs]
      rw [he]
      apply MeasurableSet.iUnion
      intro n
      have h := operational_history_meas n (fun f => H n f ∧ f ⟨n, by omega⟩ = s)
      convert h using 1
      ext ω; simp only [Set.mem_setOf_eq]; exact and_congr (hT ω n) Iff.rfl
    · have : E s = ∅ := by ext ω; simp [E,hs]
      rw [this]; exact MeasurableSet.empty
  have hF (s : State) : MeasurableSet (F s) := by
    by_cases hs : s.phase = .coinOracle k
    · let u : State := {s with oracleUsed := s.oracleUsed+1, phase := .coinFair k}
      let v : State := coinReturn k false {u with fairUsed := u.fairUsed+1}
      have he : F s = ⋃ n, {ω | T ω = some n ∧ allSuppressedRun ω n = s ∧ allSuppressedRun ω (n+1) = u ∧ allSuppressedRun ω (n+2) = v} := by
        ext ω; simp [F,hs,u,v]
      rw [he]
      apply MeasurableSet.iUnion
      intro n
      let K : (Fin (n+3) → State) → Prop := fun f =>
        H n (fun j : Fin (n+1) => f ⟨j.val, by omega⟩) ∧ f ⟨n, by omega⟩ = s ∧
        f ⟨n+1, by omega⟩ = u ∧ f ⟨n+2, by omega⟩ = v
      have h := operational_history_meas (n+2) K
      convert h using 1
      ext ω; simp only [K,Set.mem_setOf_eq]; exact and_congr (hT ω n) Iff.rfl
    · have : F s = ∅ := by ext ω; simp [F,hs]
      rw [this]; exact MeasurableSet.empty
  have hdisjE : Pairwise (fun s t => Disjoint (E s) (E t)) := by
    intro s t hst
    apply Set.disjoint_left.mpr
    rintro ω ⟨n,htn,hs,_⟩ ⟨m,htm,ht,_⟩
    have : n = m := Option.some.inj (htn.symm.trans htm)
    subst m
    exact hst (hs.symm.trans ht)
  have hdisjF : Pairwise (fun s t => Disjoint (F s) (F t)) := by
    intro s t hst
    apply Set.disjoint_left.mpr
    rintro ω ⟨n,htn,hs,_,_,_⟩ ⟨m,htm,ht,_,_,_⟩
    have : n = m := Option.some.inj (htn.symm.trans htm)
    subst m
    exact hst (hs.symm.trans ht)
  have hfac (s : State) : entropyLaw B (F s) = entropyLaw B (E s) * (B/2) := by
    by_cases hs : s.phase = .coinOracle k
    · have h := suppressed_stopping_coin_zero B hB T H hT s k hs
      simpa [E,F,hs] using h
    · have he : E s = ∅ := by ext ω; simp [E,hs]
      have hf : F s = ∅ := by ext ω; simp [F,hs]
      rw [he,hf,measure_empty,zero_mul]
  have he : {ω | ∃ n, T ω = some n ∧ (allSuppressedRun ω n).phase = .coinOracle k} = ⋃ s, E s := by
    ext ω
    simp only [Set.mem_setOf_eq,Set.mem_iUnion,E]
    constructor
    · rintro ⟨n,ht,hp⟩; exact ⟨allSuppressedRun ω n,n,ht,rfl,hp⟩
    · rintro ⟨s,n,ht,hr,hp⟩; exact ⟨n,ht,by simpa [hr] using hp⟩
  have hf : {ω | ∃ n, T ω = some n ∧ (allSuppressedRun ω n).phase = .coinOracle k ∧
      let s := allSuppressedRun ω n
      let u : State := {s with oracleUsed := s.oracleUsed+1, phase := .coinFair k}
      let v : State := coinReturn k false {u with fairUsed := u.fairUsed+1}
      allSuppressedRun ω (n+1) = u ∧ allSuppressedRun ω (n+2) = v} = ⋃ s, F s := by
    ext ω
    simp only [Set.mem_setOf_eq,Set.mem_iUnion,F]
    constructor
    · rintro ⟨n,ht,hp,hu,hv⟩; exact ⟨allSuppressedRun ω n,n,ht,rfl,hp,hu,hv⟩
    · rintro ⟨s,n,ht,hr,hp,hu,hv⟩
      subst s
      exact ⟨n,ht,hp,hu,hv⟩
  rw [hf,he,measure_iUnion hdisjF hF,measure_iUnion hdisjE hE]
  simp_rw [hfac]
  exact ENNReal.tsum_mul_right
