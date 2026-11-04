-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_bounded_negative_test_grid_l2_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:07:04.051137+00:00
-- url     : https://prove2.me/submissions/9bde5dc6-8b99-4fe1-9672-d63bfc36e207

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_bounded_horizon_negative_grid_l2_uniform_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- Any finite, nonnegative bounded test vanishing above a separated negative
band inherits the original-process uniform equispaced-grid second moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → ℝ≥0∞) (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (hf : ∀ y : ℝ, f y ≤ if y ≤ -ε then M else 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        ∀ n : ℕ, (n : ℝ) * h ≤ T →
        (∫⁻ ω, (∑ i ∈ Finset.range n,
          f (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal h) ω -
              X.X ((i : ℝ≥0) * Real.toNNReal h) ω)) ^ 2 ∂P) ≤
          M ^ 2 * (ENNReal.ofReal (C * T) +
            (ENNReal.ofReal (C * T)) ^ 2) := by
  obtain ⟨C, hC, hRate⟩ :=
    avram_p2_original_bounded_horizon_negative_grid_l2_uniform_bound X ε hε T hT
  refine ⟨C, hC, ?_⟩
  filter_upwards [hRate] with h hCount
  intro n hn
  let z : ℕ → Ω → ℝ := fun i ω =>
    X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal h) ω -
      X.X ((i : ℝ≥0) * Real.toNNReal h) ω
  let a : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    ({v : Ω | z i v ≤ -ε}).indicator (fun _ => (1 : ℝ≥0∞)) ω
  have hXm : ∀ t, Measurable (X.X t) := fun t =>
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hZm (i : ℕ) : Measurable (z i) := (hXm _).sub (hXm _)
  have hAi (i : ℕ) : Measurable (a i) :=
    measurable_const.indicator
      ((measurableSet_Iic : MeasurableSet (Iic (-ε))).preimage (hZm i))
  have hCountMeas : Measurable (fun ω => (∑ i ∈ Finset.range n, a i ω) ^ 2) :=
    ((Finset.range n).measurable_sum (by
      intro i hi
      exact hAi i)).pow_const _
  have hPoint (ω : Ω) :
      (∑ i ∈ Finset.range n, f (z i ω)) ≤
        M * (∑ i ∈ Finset.range n, a i ω) := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, M * a i ω := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hc : z i ω ≤ -ε
        · have hw : ω ∈ {v : Ω | z i v ≤ -ε} := hc
          simpa [a, Set.indicator_of_mem hw, hc] using hf (z i ω)
        · have hw : ω ∉ {v : Ω | z i v ≤ -ε} := hc
          simpa [a, Set.indicator_of_notMem hw, hc] using hf (z i ω)
      _ = M * (∑ i ∈ Finset.range n, a i ω) := by rw [Finset.mul_sum]
  have hSq (ω : Ω) :
      (∑ i ∈ Finset.range n, f (z i ω)) ^ 2 ≤
        M ^ 2 * (∑ i ∈ Finset.range n, a i ω) ^ 2 := by
    calc
      _ ≤ (M * ∑ i ∈ Finset.range n, a i ω) ^ 2 := by
        gcongr <;> exact hPoint ω
      _ = M ^ 2 * (∑ i ∈ Finset.range n, a i ω) ^ 2 := mul_pow M _ 2
  calc
    (∫⁻ ω, (∑ i ∈ Finset.range n, f (z i ω)) ^ 2 ∂P) ≤
      ∫⁻ ω, M ^ 2 * (∑ i ∈ Finset.range n, a i ω) ^ 2 ∂P :=
        lintegral_mono hSq
    _ = M ^ 2 * (∫⁻ ω, (∑ i ∈ Finset.range n, a i ω) ^ 2 ∂P) :=
      lintegral_const_mul _ hCountMeas
    _ ≤ M ^ 2 * (ENNReal.ofReal (C * T) +
        (ENNReal.ofReal (C * T)) ^ 2) := by
      exact mul_le_mul_of_nonneg_left (hCount n hn) (by positivity)
