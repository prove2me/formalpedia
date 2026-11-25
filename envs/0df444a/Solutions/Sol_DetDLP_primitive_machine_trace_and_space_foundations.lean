-- Prove2me | solution 1 for DetDLP.primitive_machine_trace_and_space_foundations
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T14:29:07.628952+00:00
-- url     : https://prove2.me/submissions/52093647-989e-4b4e-a42d-abdbf03470e0

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_DetDLP_Machine

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP

private theorem trace_det {α : Type} (step : α → Option α) :
    ∀ (k : ℕ) (a b₁ b₂ : α), Trace step k a b₁ → Trace step k a b₂ → b₁ = b₂ := by
  intro k
  induction k with
  | zero =>
    intro a b₁ b₂ h₁ h₂
    cases h₁
    cases h₂
    rfl
  | succ k ih =>
    intro a b₁ b₂ h₁ h₂
    cases h₁ with
    | cons hs₁ ht₁ =>
      cases h₂ with
      | cons hs₂ ht₂ =>
        rw [hs₁] at hs₂
        injection hs₂ with hmid
        subst hmid
        exact ih _ _ _ ht₁ ht₂

private theorem trace_halt_unique {α : Type} (step : α → Option α) :
    ∀ (k₁ k₂ : ℕ) (a b₁ b₂ : α),
      Trace step k₁ a b₁ → step b₁ = none →
      Trace step k₂ a b₂ → step b₂ = none →
      k₁ = k₂ ∧ b₁ = b₂ := by
  intro k₁
  induction k₁ with
  | zero =>
    intro k₂ a b₁ b₂ h₁ hs₁ h₂ hs₂
    cases h₁
    cases h₂ with
    | refl => exact ⟨rfl, rfl⟩
    | cons hstep _ =>
      rw [hs₁] at hstep
      cases hstep
  | succ k₁ ih =>
    intro k₂ a b₁ b₂ h₁ hs₁ h₂ hs₂
    cases h₁ with
    | cons hstep₁ ht₁ =>
      cases h₂ with
      | refl =>
        rw [hs₂] at hstep₁
        cases hstep₁
      | cons hstep₂ ht₂ =>
        rw [hstep₁] at hstep₂
        injection hstep₂ with hmid
        subst hmid
        obtain ⟨hk, hb⟩ := ih _ _ _ _ ht₁ hs₁ ht₂ hs₂
        exact ⟨congrArg (· + 1) hk, hb⟩

private theorem locatedStep_eq_none_of_halted (M : PrimitiveMachine)
    (c : LocatedCfg M) (b : Bool) (h : c.config.state = Sum.inl b) :
    locatedStep M c = none := by
  unfold locatedStep PrimitiveMachine.step
  rw [h]
  rfl

private def locatedInv {M : PrimitiveMachine} (c : LocatedCfg M) : Prop :=
  ∀ i : Fin M.tapeCount, c.lower i ≤ c.position i ∧ c.position i ≤ c.upper i

private theorem locatedInit_inv (M : PrimitiveMachine) (input : List Bool) :
    locatedInv (locatedInit M input) := by
  intro i
  simp only [locatedInit]
  split_ifs
  · exact ⟨le_rfl, Int.natCast_nonneg _⟩
  · exact ⟨le_rfl, le_rfl⟩

private theorem visitedSpace_locatedInit_le (M : PrimitiveMachine) (input : List Bool) :
    visitedSpace (locatedInit M input) ≤ input.length + M.tapeCount := by
  unfold visitedSpace locatedInit
  simp only [sub_zero]
  have hsum :
      (∑ i : Fin M.tapeCount,
        ((if i = M.inputTape then (Int.ofNat (input.length - 1)) else 0) + 1).toNat) =
      ∑ i : Fin M.tapeCount, (if i = M.inputTape then (input.length - 1) + 1 else 1) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    split_ifs <;> rfl
  rw [hsum]
  have hle :
      (∑ i : Fin M.tapeCount, (if i = M.inputTape then (input.length - 1) + 1 else 1)) ≤
      ∑ i : Fin M.tapeCount, ((if i = M.inputTape then input.length else 0) + 1) := by
    refine Finset.sum_le_sum ?_
    intro i _
    split_ifs <;> omega
  refine le_trans hle ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one]
  have hite :
      (∑ i : Fin M.tapeCount, if i = M.inputTape then input.length else 0) = input.length := by
    simp
  omega

private theorem headDisplacement_bounds (action : Turing.TM0.Stmt (Option Bool)) :
    -1 ≤ headDisplacement action ∧ headDisplacement action ≤ 1 := by
  cases action with
  | move d =>
    cases d <;> simp [headDisplacement]
  | write _ =>
    simp [headDisplacement]

private theorem monitor_inv_and_space {M : PrimitiveMachine} (c : LocatedCfg M)
    (cfg' : M.Cfg) (hinv : locatedInv c) :
    locatedInv (c.monitor cfg') ∧
      visitedSpace (c.monitor cfg') ≤ visitedSpace c + 1 := by
  unfold LocatedCfg.monitor
  cases hst : c.config.state with
  | inl b =>
    simp only [Sum.elim_inl]
    exact ⟨hinv, Nat.le_succ _⟩
  | inr q =>
    simp only [Sum.elim_inr]
    cases htr : M.transition q (c.config.tapes (M.scan q)).head with
    | inl ans =>
      simp only [Sum.elim_inl]
      exact ⟨hinv, Nat.le_succ _⟩
    | inr qa =>
      simp only [Sum.elim_inr]
      set i := M.scan q
      set action := qa.2
      set pos := c.position i + headDisplacement action
      have hdisp := headDisplacement_bounds action
      have hi := hinv i
      constructor
      · intro j
        by_cases hj : j = i
        · subst hj
          simp only [Function.update, ↓reduceDIte]
          exact ⟨min_le_right _ _, le_max_right _ _⟩
        · simp only [Function.update, hj, ↓reduceDIte]
          exact hinv j
      · unfold visitedSpace
        have hterm_le :
            ∀ j : Fin M.tapeCount,
              ((Function.update c.upper i (max (c.upper i) pos) j -
                Function.update c.lower i (min (c.lower i) pos) j + 1).toNat) ≤
              (c.upper j - c.lower j + 1).toNat + (if j = i then 1 else 0) := by
          intro j
          by_cases hj : j = i
          · subst hj
            simp only [Function.update, ↓reduceDIte, ↓reduceIte]
            have h1 : c.lower i ≤ c.position i := hi.1
            have h2 : c.position i ≤ c.upper i := hi.2
            have h3 : -1 ≤ headDisplacement action := hdisp.1
            have h4 : headDisplacement action ≤ 1 := hdisp.2
            omega
          · simp only [Function.update, hj, ↓reduceDIte, ↓reduceIte, add_zero]
            exact le_rfl
        have hsum_le := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm_le j)
        rw [Finset.sum_add_distrib] at hsum_le
        have hite : (∑ j : Fin M.tapeCount, if j = i then 1 else 0) = 1 := by
          simp
        rw [hite] at hsum_le
        exact hsum_le

private theorem locatedStep_inv_and_space {M : PrimitiveMachine} (c c' : LocatedCfg M)
    (hstep : locatedStep M c = some c') (hinv : locatedInv c) :
    locatedInv c' ∧ visitedSpace c' ≤ visitedSpace c + 1 := by
  unfold locatedStep at hstep
  cases h : M.step c.config with
  | none =>
    rw [h] at hstep
    cases hstep
  | some cfg' =>
    rw [h] at hstep
    simp only [Option.map_some, Option.some.injEq] at hstep
    subst hstep
    exact monitor_inv_and_space c cfg' hinv

private theorem trace_inv_and_space (M : PrimitiveMachine) (input : List Bool) :
    ∀ (k : ℕ) (c : LocatedCfg M),
      Trace (locatedStep M) k (locatedInit M input) c →
      locatedInv c ∧ visitedSpace c ≤ visitedSpace (locatedInit M input) + k := by
  have hgen :
      ∀ (k : ℕ) (a c : LocatedCfg M),
        Trace (locatedStep M) k a c →
        locatedInv a →
        locatedInv c ∧ visitedSpace c ≤ visitedSpace a + k := by
    intro k
    induction k with
    | zero =>
      intro a c htr hinv
      cases htr
      exact ⟨hinv, by omega⟩
    | succ k ih =>
      intro a c htr hinv
      cases htr with
      | cons hstep hrest =>
        obtain ⟨hinv_b, hsp_b⟩ := locatedStep_inv_and_space a _ hstep hinv
        obtain ⟨hinv_c, hsp_c⟩ := ih _ _ hrest hinv_b
        exact ⟨hinv_c, by omega⟩
  intro k c htr
  exact hgen k (locatedInit M input) c htr (locatedInit_inv M input)

private def idHaltingMachine : PrimitiveMachine where
  tapeCount := 1
  stateCount := 1
  inputTape := ⟨0, Nat.zero_lt_one⟩
  start := ⟨0, Nat.zero_lt_one⟩
  scan _ := ⟨0, Nat.zero_lt_one⟩
  transition _ _ := Sum.inl true

/-- Fundamental execution, determinism, and space-time complexity laws for `PrimitiveMachine`,
`Trace`, `locatedStep`, `visitedSpace`, and `RunsWithin`:
(1) Step-count determinism of `Trace`.
(2) Unique halting step and unique final configuration of `Trace` across all step counts.
(3) Unique halting time and final configuration for any `PrimitiveMachine` execution from `locatedInit`.
(4) Initial configuration space bound: `visitedSpace (locatedInit M input) ≤ input.length + M.tapeCount`.
(5) Space-Time Bounding Theorem: at step `k`, `visitedSpace c ≤ input.length + M.tapeCount + k`.
(6) Automatic Space Certificate for `RunsWithin`: any halting run of length `time ≤ τ` with
    `input.length + M.tapeCount + time ≤ σ` automatically satisfies `RunsWithin M out input output τ σ`.
(7) Monotonicity of `RunsWithin` in time and space budgets `(τ, σ)`.
(8) Explicit Halting `PrimitiveMachine` Construction: there exists a concrete `PrimitiveMachine`
    halting with `RunsWithin M out input input 1 (input.length + 2)` on every input. -/
theorem solution :
    (∀ {α : Type} (step : α → Option α) (k : ℕ) (a b₁ b₂ : α),
      Trace step k a b₁ → Trace step k a b₂ → b₁ = b₂) ∧
    (∀ {α : Type} (step : α → Option α) (k₁ k₂ : ℕ) (a b₁ b₂ : α),
      Trace step k₁ a b₁ → step b₁ = none →
      Trace step k₂ a b₂ → step b₂ = none →
      k₁ = k₂ ∧ b₁ = b₂) ∧
    (∀ (M : PrimitiveMachine) (time₁ time₂ : ℕ) (input : List Bool)
        (final₁ final₂ : LocatedCfg M) (b₁ b₂ : Bool),
      Trace (locatedStep M) time₁ (locatedInit M input) final₁ →
      final₁.config.state = Sum.inl b₁ →
      Trace (locatedStep M) time₂ (locatedInit M input) final₂ →
      final₂.config.state = Sum.inl b₂ →
      time₁ = time₂ ∧ final₁ = final₂) ∧
    (∀ (M : PrimitiveMachine) (input : List Bool),
      visitedSpace (locatedInit M input) ≤ input.length + M.tapeCount) ∧
    (∀ (M : PrimitiveMachine) (input : List Bool) (k : ℕ) (c : LocatedCfg M),
      Trace (locatedStep M) k (locatedInit M input) c →
      visitedSpace c ≤ input.length + M.tapeCount + k) ∧
    (∀ (M : PrimitiveMachine) (out : Fin M.tapeCount) (input output : List Bool)
        (τ σ : ℝ) (time : ℕ) (final : LocatedCfg M) (b : Bool),
      Trace (locatedStep M) time (locatedInit M input) final →
      final.config.state = Sum.inl b →
      final.config.tapes out = Turing.Tape.mk₁ (output.map some) →
      (time : ℝ) ≤ τ →
      ((input.length + M.tapeCount + time : ℕ) : ℝ) ≤ σ →
      RunsWithin M out input output τ σ) ∧
    (∀ (M : PrimitiveMachine) (out : Fin M.tapeCount) (input output : List Bool)
        (τ₁ σ₁ τ₂ σ₂ : ℝ),
      RunsWithin M out input output τ₁ σ₁ → τ₁ ≤ τ₂ → σ₁ ≤ σ₂ →
      RunsWithin M out input output τ₂ σ₂) ∧
    (∃ (M : PrimitiveMachine) (out : Fin M.tapeCount),
      ∀ (input : List Bool),
        RunsWithin M out input input 1 ((input.length + 2 : ℕ) : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α step k a b₁ b₂ h₁ h₂
    exact trace_det step k a b₁ b₂ h₁ h₂
  · intro α step k₁ k₂ a b₁ b₂ h₁ hs₁ h₂ hs₂
    exact trace_halt_unique step k₁ k₂ a b₁ b₂ h₁ hs₁ h₂ hs₂
  · intro M time₁ time₂ input final₁ final₂ b₁ b₂ h₁ hs₁ h₂ hs₂
    exact trace_halt_unique (locatedStep M) time₁ time₂ (locatedInit M input) final₁ final₂
      h₁ (locatedStep_eq_none_of_halted M final₁ b₁ hs₁)
      h₂ (locatedStep_eq_none_of_halted M final₂ b₂ hs₂)
  · intro M input
    exact visitedSpace_locatedInit_le M input
  · intro M input k c htr
    have h1 := (trace_inv_and_space M input k c htr).2
    have h2 := visitedSpace_locatedInit_le M input
    omega
  · intro M out input output τ σ time final b htr hst htape htime hsp
    refine ⟨time, final, htr, ⟨b, hst⟩, htape, htime, ?_⟩
    intro k c hk htr_k
    have hsp_k : visitedSpace c ≤ input.length + M.tapeCount + k := by
      have h1 := (trace_inv_and_space M input k c htr_k).2
      have h2 := visitedSpace_locatedInit_le M input
      omega
    have hsp_time : visitedSpace c ≤ input.length + M.tapeCount + time := by
      omega
    exact le_trans (Nat.cast_le.mpr hsp_time) hsp
  · intro M out input output τ₁ σ₁ τ₂ σ₂ hrun hτ hσ
    rcases hrun with ⟨time, final, htr, hhalt, htape, htime, hsp⟩
    refine ⟨time, final, htr, hhalt, htape, le_trans htime hτ, ?_⟩
    intro k c hk htr_k
    exact le_trans (hsp k c hk htr_k) hσ
  · refine ⟨idHaltingMachine, ⟨0, Nat.zero_lt_one⟩, ?_⟩
    intro input
    let c₀ := locatedInit idHaltingMachine input
    let c₁ : LocatedCfg idHaltingMachine :=
      { c₀ with config := ⟨Sum.inl true, c₀.config.tapes⟩ }
    have hstep : locatedStep idHaltingMachine c₀ = some c₁ := rfl
    have htr : Trace (locatedStep idHaltingMachine) 1 c₀ c₁ :=
      Trace.cons hstep (Trace.refl c₁)
    refine ⟨1, c₁, htr, ⟨true, rfl⟩, rfl, by norm_num, ?_⟩
    intro k c hk htr_k
    have hsp_k : visitedSpace c ≤ input.length + idHaltingMachine.tapeCount + k := by
      have h1 := (trace_inv_and_space idHaltingMachine input k c htr_k).2
      have h2 := visitedSpace_locatedInit_le idHaltingMachine input
      omega
    have hsp_1 : visitedSpace c ≤ input.length + 2 := by
      change visitedSpace c ≤ input.length + 1 + k at hsp_k
      omega
    exact Nat.cast_le.mpr hsp_1
