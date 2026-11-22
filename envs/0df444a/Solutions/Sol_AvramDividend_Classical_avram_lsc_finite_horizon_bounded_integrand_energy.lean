-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_finite_horizon_bounded_integrand_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T22:38:22.25466+00:00
-- url     : https://prove2.me/submissions/f5213226-a55d-4d40-9d93-eff051fbcf05

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Every uniformly bounded real integrand has finite square energy
on each finite time interval under a probability measure. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : Ω → ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ ω s, |F ω s| ≤ M)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hle : ∀ ω s, (‖F ω s‖₊ : ℝ≥0∞) ≤ (Real.toNNReal M : ℝ≥0∞) := by
    intro ω s
    refine ENNReal.coe_le_coe.mpr ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal M hM,
      coe_nnnorm, Real.norm_eq_abs]
    exact hBound ω s
  have hsq : ∀ ω s, (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ≤
      (Real.toNNReal M : ℝ≥0∞) ^ 2 := by
    intro ω s
    exact pow_le_pow_left' (hle ω s) 2
  calc
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (Real.toNNReal M : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hsq ω s
    _ < ⊤ := by
      simp only [lintegral_const, Measure.restrict_apply_univ,
        Real.volume_Icc, sub_zero, measure_univ, mul_one]
      exact ENNReal.mul_lt_top
        (ENNReal.pow_lt_top ENNReal.coe_lt_top)
        ENNReal.ofReal_lt_top

