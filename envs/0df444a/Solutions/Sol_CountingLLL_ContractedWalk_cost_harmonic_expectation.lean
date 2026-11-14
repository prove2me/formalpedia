-- Prove2me | solution 1 for CountingLLL.ContractedWalk.cost_harmonic_expectation
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:01:23.870188+00:00
-- url     : https://prove2.me/submissions/550e6b36-b84c-41de-a1d6-1e770db86f39

import Definitions.Def_CountingLLL_ContractedGF
import Definitions.Def_CountingLLL_ContractedCost
import Theorems.Thm_CountingLLL_ContractedWalk_absorption_and_expected_changes
import Theorems.Thm_CountingLLL_ContractedWalk_weighted_increases_eq
import Theorems.Thm_CountingLLL_ContractedWalk_weighted_increases_harmonic
set_option autoImplicit false
open MeasureTheory CountingLLL.ContractedWalk
open scoped BigOperators ENNReal

private theorem level_ext (ω ω' : Tape) (i t : ℕ) (h : ∀ k < t, ω k = ω' k) : level ω i t = level ω' i t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprev : ∀ k < t, ω k = ω' k := by intro k hk; exact h k (by omega)
    have hnow := h t (by omega)
    simp only [level, ih hprev, hnow]

private theorem prefix_meas (t : ℕ) (P : Tape → Prop)
    (hP : ∀ ω ω', (∀ k < t, ω k = ω' k) → (P ω ↔ P ω')) : MeasurableSet {ω | P ω} := by
  classical
  let f : Tape → (Fin t → Bool) := fun ω j => ω j
  have hf : Measurable f := measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
  let F : Set (Fin t → Bool) := {x | ∃ ω : Tape, f ω = x ∧ P ω}
  have heq : f ⁻¹' F = {ω : Tape | P ω} := by
    ext ω
    constructor
    · rintro ⟨ω', heq, hn⟩
      have he : ∀ k < t, ω k = ω' k := by intro k hk; exact (congrFun heq ⟨k,hk⟩).symm
      exact (hP ω ω' he).2 hn
    · intro hn; exact ⟨ω, rfl, hn⟩
  rw [← heq]
  exact MeasurableSet.of_discrete.preimage hf

private def countAt (ω : Tape) (i t : ℕ) : ℕ :=
  ∑ k ∈ Finset.range t, if level ω i k ≠ 0 ∧ ω k = true then 1 else 0

private theorem count_ext (ω ω' : Tape) (i t : ℕ) (h : ∀ k < t, ω k = ω' k) : countAt ω i t = countAt ω' i t := by
  unfold countAt
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have he : ∀ j < k, ω j = ω' j := by intro j hj; exact h j (by omega)
  rw [level_ext ω ω' i k he, h k hk']

private theorem finite_event (i t : ℕ) (P : ℕ → ℕ → Prop) :
    MeasurableSet {ω : Tape | P (level ω i t) (countAt ω i t)} := by
  apply prefix_meas t
  intro ω ω' h
  rw [level_ext ω ω' i t h, count_ext ω ω' i t h]

private theorem stop_meas (i : ℕ) : MeasurableSet {ω : Tape | ∃ t, level ω i t = 0} := by
  have heq : {ω : Tape | ∃ t, level ω i t = 0} = ⋃ t : ℕ, {ω : Tape | level ω i t = 0} := by ext ω; simp
  rw [heq]
  exact MeasurableSet.iUnion fun t => finite_event i t (fun level _ => level = 0)


private theorem bitLaw_probability' (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

/-- The source weighted-change expectation times θ equals the harmonic expectation. -/
theorem solution (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1/3) :
    expectedWeightedChanges (ENNReal.ofReal θ) 3 2 * ENNReal.ofReal θ =
      ∫⁻ ω, ∑ k ∈ Finset.range (upwardCount ω 3), (((2+k : ℕ) : ℝ≥0∞)⁻¹) ∂tapeLaw (ENNReal.ofReal θ) := by
  have hp : ENNReal.ofReal θ ≤ 1 := by
    have hreal : θ ≤ (1:ℝ) := by linarith
    simpa using ENNReal.ofReal_le_ofReal hreal
  letI : IsProbabilityMeasure (bitLaw (ENNReal.ofReal θ)) := bitLaw_probability' _ hp
  letI : IsProbabilityMeasure (tapeLaw (ENNReal.ofReal θ)) := by unfold tapeLaw; infer_instance
  have hstop : ∀ᵐ ω ∂tapeLaw (ENNReal.ofReal θ), ∃ t, level ω 3 t = 0 := by
    apply ae_iff.mpr
    have h := measure_compl (μ := tapeLaw (ENNReal.ofReal θ)) (stop_meas 3) (by simp)
    rw [measure_univ, (absorption_and_expected_changes θ hθ0 hθ1 3).1] at h
    change tapeLaw (ENNReal.ofReal θ) ({ω : Tape | ∃ t, level ω 3 t = 0}ᶜ) = 0
    simpa using h
  rw [← weighted_increases_eq (ENNReal.ofReal θ) hp 3 2]
  unfold expectedWeightedIncreases
  apply lintegral_congr_ae
  filter_upwards [hstop] with ω hω
  exact weighted_increases_harmonic ω 3 2 hω
