-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.execution_measurable
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:07:54.082801+00:00
-- url     : https://prove2.me/submissions/1892c1ad-2023-4c80-81a7-f6f64b26dac4

import Definitions.Def_CountingLLL_ReciprocalTest

set_option autoImplicit false
open MeasureTheory CountingLLL.ReciprocalTest
open scoped ENNReal

private theorem step_ext (ω ω' : Entropy) (s : State)
    (ho : ω.1 s.oracleUsed = ω'.1 s.oracleUsed)
    (hf : ω.2.1 s.fairUsed = ω'.2.1 s.fairUsed)
    (hu : ω.2.2 (s.j-1,s.uniformUsed) = ω'.2.2 (s.j-1,s.uniformUsed)) : step ω s = step ω' s := by
  cases h : s.phase <;> simp [step, h, ho, hf, hu]

private theorem step_bounds (ω : Entropy) (s : State) :
    (step ω s).oracleUsed ≤ s.oracleUsed+1 ∧
    (step ω s).fairUsed ≤ s.fairUsed+1 ∧
    (step ω s).uniformUsed ≤ s.uniformUsed+1 ∧
    (step ω s).j ≤ s.j+2 := by
  cases h : s.phase with
  | start => simp only [step, h]; split <;> simp
  | initialCheck => simp only [step, h]; split <;> simp
  | loop => simp only [step, h]; split <;> simp
  | coinOracle k => cases k <;> simp only [step, h] <;> split <;> simp [coinReturn]
  | coinFair k => cases k <;> simp only [step, h] <;> split <;> simp [coinReturn]
  | uniformCheck => simp only [step, h]; split <;> simp
  | done b => simp [step, h]

private theorem iterate_ext (ω ω' : Entropy) (t : ℕ) : ∀ s : State,
    (∀ i < s.oracleUsed+t, ω.1 i = ω'.1 i) →
    (∀ i < s.fairUsed+t, ω.2.1 i = ω'.2.1 i) →
    (∀ n < s.j+2*t+1, ∀ i < s.uniformUsed+t, ω.2.2 (n,i) = ω'.2.2 (n,i)) →
    (step ω)^[t] s = (step ω')^[t] s := by
  induction t with
  | zero => intro s ho hf hu; rfl
  | succ t ih =>
    intro s ho hf hu
    have hstep := step_ext ω ω' s (ho _ (by omega)) (hf _ (by omega)) (hu _ (by omega) _ (by omega))
    have hb := step_bounds ω s
    have ho' : ∀ i < (step ω s).oracleUsed+t, ω.1 i = ω'.1 i := by intro i hi; exact ho i (by omega)
    have hf' : ∀ i < (step ω s).fairUsed+t, ω.2.1 i = ω'.2.1 i := by intro i hi; exact hf i (by omega)
    have hu' : ∀ n < (step ω s).j+2*t+1, ∀ i < (step ω s).uniformUsed+t, ω.2.2 (n,i) = ω'.2.2 (n,i) := by
      intro n hn i hi
      exact hu n (by omega) i (by omega)
    simpa [Function.iterate_succ_apply, hstep] using ih (step ω s) ho' hf' hu'

private theorem finite_event (t : ℕ) (A : State → Prop) : MeasurableSet {ω : Entropy | A (run ω t)} := by
  classical
  let pref : Entropy → ((Fin t → Bool) × (Fin t → Bool) × ((q : Fin (2*t+1) × Fin t) → Fin (q.1.val+1))) :=
    fun ω => (fun i => ω.1 i.val, fun i => ω.2.1 i.val, fun q => ω.2.2 (q.1.val,q.2.val))
  have hm : Measurable pref := by
    apply Measurable.prodMk
    · exact measurable_pi_lambda _ (fun i => (measurable_pi_apply i.val).comp measurable_fst)
    · apply Measurable.prodMk
      · exact measurable_pi_lambda _ (fun i => (measurable_pi_apply i.val).comp (measurable_fst.comp measurable_snd))
      · exact measurable_pi_lambda _ (fun q => (measurable_pi_apply (q.1.val,q.2.val)).comp (measurable_snd.comp measurable_snd))
  let T := {p | ∃ ω : Entropy, A (run ω t) ∧ pref ω = p}
  have heq : {ω : Entropy | A (run ω t)} = pref ⁻¹' T := by
    ext ω
    constructor
    · intro hω; exact ⟨ω, hω, rfl⟩
    · rintro ⟨ω', hω', hpre⟩
      have ho : ∀ i < t, ω.1 i = ω'.1 i := by
        intro i hi
        exact (congrFun (congrArg Prod.fst hpre) ⟨i,hi⟩).symm
      have hf : ∀ i < t, ω.2.1 i = ω'.2.1 i := by
        intro i hi
        exact (congrFun (congrArg Prod.fst (congrArg Prod.snd hpre)) ⟨i,hi⟩).symm
      have hu : ∀ n < 2*t+1, ∀ i < t, ω.2.2 (n,i) = ω'.2.2 (n,i) := by
        intro n hn i hi
        exact (congrFun (congrArg Prod.snd (congrArg Prod.snd hpre)) (⟨n,hn⟩, ⟨i,hi⟩)).symm
      have hh := iterate_ext ω ω' t initial (by simpa [initial] using ho) (by simpa [initial] using hf) (by simpa [initial] using hu)
      simpa [run, hh] using hω'
  rw [heq]
  exact MeasurableSet.of_discrete.preimage hm

private theorem returns_measurable (b : Bool) : MeasurableSet {ω : Entropy | Returns ω b} := by
  have h : {ω : Entropy | Returns ω b} = ⋃ t : ℕ, {ω : Entropy | (run ω t).phase = .done b} := by ext ω; simp [Returns]
  rw [h]
  exact MeasurableSet.iUnion (fun t => finite_event t (fun s => s.phase = .done b))

private theorem halts_measurable : MeasurableSet {ω : Entropy | Halts ω} := by
  have h : {ω : Entropy | Halts ω} = {ω : Entropy | Returns ω false} ∪ {ω : Entropy | Returns ω true} := by
    ext ω; simp only [Halts, Returns, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨t, b, hb⟩
      cases b with
      | false => exact Or.inl ⟨t, hb⟩
      | true => exact Or.inr ⟨t, hb⟩
    · rintro (⟨t, ht⟩ | ⟨t, ht⟩) <;> exact ⟨t, _, ht⟩
  rw [h]
  exact (returns_measurable false).union (returns_measurable true)

private noncomputable def final (ω : Entropy) : State := by
  classical
  exact if h : Halts ω then run ω (Nat.find h) else initial

private theorem final_event_measurable (A : State → Prop) : MeasurableSet {ω : Entropy | A (final ω)} := by
  classical
  let doneState : State → Prop := fun s => ∃ b, s.phase = .done b
  let events : ℕ → Set Entropy := fun t => {ω |
    doneState (run ω t) ∧ (∀ j < t, ¬ doneState (run ω j)) ∧ A (run ω t)}
  have hevents : ∀ t, MeasurableSet (events t) := by
    intro t
    have h1 := finite_event t (fun st => doneState st ∧ A st)
    have h2 : MeasurableSet (⋂ j : Fin t, {ω : Entropy | ¬ doneState (run ω j.val)}) :=
      MeasurableSet.iInter fun j => finite_event j.val (fun st => ¬ doneState st)
    have heq : events t = {ω : Entropy | doneState (run ω t) ∧ A (run ω t)} ∩
        (⋂ j : Fin t, {ω : Entropy | ¬ doneState (run ω j.val)}) := by
      ext ω
      simp only [events, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · rintro ⟨h, hmin, hA⟩; exact ⟨⟨h,hA⟩, fun j => hmin j.val j.isLt⟩
      · rintro ⟨⟨h,hA⟩, hmin⟩; exact ⟨h, fun j hj => hmin ⟨j,hj⟩, hA⟩
    rw [heq]
    exact h1.inter h2
  have heq : {ω : Entropy | A (final ω)} =
      (({ω : Entropy | Halts ω}ᶜ) ∩ {ω | A initial}) ∪ ⋃ t, events t := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iUnion, events]
    constructor
    · intro hA
      by_cases h : Halts ω
      · right
        refine ⟨Nat.find h, Nat.find_spec h, ?_, ?_⟩
        · intro j hj; exact Nat.find_min h hj
        · simpa [final, h] using hA
      · left; exact ⟨h, by simpa [final, h] using hA⟩
    · rintro (⟨h, hA⟩ | ⟨t, ht, hmin, hA⟩)
      · simpa [final, h] using hA
      · have h : Halts ω := ⟨t, ht⟩
        have hfind : Nat.find h = t := (Nat.find_eq_iff h).mpr ⟨ht, hmin⟩
        have hf : final ω = run ω t := by
          unfold final
          rw [dif_pos h, hfind]
        rw [hf]
        exact hA
  rw [heq]
  exact ((halts_measurable.compl.inter (by by_cases h : A initial <;> simp [h]))).union (MeasurableSet.iUnion hevents)

private theorem oracleCost_measurable : Measurable oracleCost := by
  classical
  intro T hT
  have heq : oracleCost ⁻¹' T =
      ({ω : Entropy | Halts ω} ∩ {ω | ((final ω).oracleUsed : ℝ≥0∞) ∈ T}) ∪
      (if ⊤ ∈ T then {ω : Entropy | Halts ω}ᶜ else ∅) := by
    ext ω
    by_cases h : Halts ω <;> by_cases htop : (⊤ : ℝ≥0∞) ∈ T <;>
      simp [oracleCost, final, h, htop]
  rw [heq]
  have h1 := halts_measurable.inter (final_event_measurable (fun s => ((s.oracleUsed : ℝ≥0∞) ∈ T)))
  have h2 : MeasurableSet (if ⊤ ∈ T then {ω : Entropy | Halts ω}ᶜ else ∅) := by
    by_cases h : (⊤ : ℝ≥0∞) ∈ T
    · simpa only [if_pos h] using halts_measurable.compl
    · simp [h]
  exact h1.union h2


theorem solution : MeasurableSet {ω : Entropy | Halts ω} ∧ (∀ b : Bool, MeasurableSet {ω : Entropy | Returns ω b}) ∧ Measurable oracleCost := by
  exact ⟨halts_measurable, returns_measurable, oracleCost_measurable⟩
