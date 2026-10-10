-- Prove2me | solution 1 for BookProof.MollifierL2.enorm_mollify_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T22:06:07.881435+00:00
-- url     : https://prove2.me/submissions/2fc5fbf3-33fa-4063-b6c7-4645bd2b50bb

-- Generated from ChapterMollifierL2.lean — solution of BookProof.MollifierL2.enorm_mollify_sq_le
import Mathlib
import Definitions.Def_ChapterMollifierL2
open BookProof.MollifierL2




open MeasureTheory Filter ENNReal Pointwise
open scoped NNReal Topology

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

set_option maxHeartbeats 1000000 in
theorem solution (u : E → ℂ) (ρ : E → ℝ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρm : Measurable ρ)
    (hρ1 : ∫⁻ y, ENNReal.ofReal (ρ y) ∂μ = 1) (hu : StronglyMeasurable u) (x : E) :
    ‖∫ y, ρ y • (u (x - y) - u x) ∂μ‖ₑ ^ (2:ℝ)
      ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ) ∂μ := by

  set w : E → ℝ≥0∞ := fun y => ‖u (x - y) - u x‖ₑ with hw
  have hwm : AEMeasurable w μ :=
    ((hu.comp_measurable (by fun_prop)).sub stronglyMeasurable_const).measurable.enorm.aemeasurable
  have hstep1 : ‖∫ y, ρ y • (u (x - y) - u x) ∂μ‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * w y ∂μ := by
    refine le_trans (enorm_integral_le_lintegral_enorm _) (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    rw [enorm_smul]
    congr 1
    simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hρ0 y)]
  have hA : AEMeasurable (fun y => (ENNReal.ofReal (ρ y)) ^ ((1:ℝ)/2)) μ :=
    ((ENNReal.measurable_ofReal.comp hρm).pow_const _).aemeasurable
  have hB : AEMeasurable (fun y => (ENNReal.ofReal (ρ y)) ^ ((1:ℝ)/2) * w y) μ := hA.mul hwm
  have hCS : ∫⁻ y, ENNReal.ofReal (ρ y) * w y ∂μ
      ≤ (∫⁻ y, ((ENNReal.ofReal (ρ y)) ^ ((1:ℝ)/2)) ^ (2:ℝ) ∂μ) ^ ((1:ℝ)/2)
        * (∫⁻ y, ((ENNReal.ofReal (ρ y)) ^ ((1:ℝ)/2) * w y) ^ (2:ℝ) ∂μ) ^ ((1:ℝ)/2) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2)
      (by constructor <;> norm_num) hA hB
    refine le_trans (le_of_eq ?_) h
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hsq1 : ∀ y : E, ((ENNReal.ofReal (ρ y)) ^ ((1:ℝ)/2)) ^ (2:ℝ) = ENNReal.ofReal (ρ y) := by
    intro y
    rw [← ENNReal.rpow_mul]
    norm_num
  have hsq2 : ∀ y : E, ((ENNReal.ofReal (ρ y)) ^ ((1:ℝ)/2) * w y) ^ (2:ℝ)
      = ENNReal.ofReal (ρ y) * w y ^ (2:ℝ) := by
    intro y
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
    norm_num
  simp only [hsq1, hsq2] at hCS
  rw [hρ1] at hCS
  simp only [ENNReal.one_rpow, one_mul] at hCS
  calc ‖∫ y, ρ y • (u (x - y) - u x) ∂μ‖ₑ ^ (2:ℝ)
      ≤ ((∫⁻ y, ENNReal.ofReal (ρ y) * w y ^ (2:ℝ) ∂μ) ^ ((1:ℝ)/2)) ^ (2:ℝ) :=
        ENNReal.rpow_le_rpow (hstep1.trans hCS) (by norm_num)
    _ = ∫⁻ y, ENNReal.ofReal (ρ y) * w y ^ (2:ℝ) ∂μ := by
        rw [← ENNReal.rpow_mul]
        norm_num
