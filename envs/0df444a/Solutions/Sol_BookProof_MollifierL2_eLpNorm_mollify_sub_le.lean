-- Prove2me | solution 1 for BookProof.MollifierL2.eLpNorm_mollify_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T22:06:11.802644+00:00
-- url     : https://prove2.me/submissions/659e7438-f941-4277-ada7-b6c3cdd24376

-- Generated from ChapterMollifierL2.lean — solution of BookProof.MollifierL2.eLpNorm_mollify_sub_le
import Mathlib
import Definitions.Def_ChapterMollifierL2
import Theorems.Thm_BookProof_MollifierL2_enorm_mollify_sq_le
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
theorem solution (u : E → ℂ) (hu : StronglyMeasurable u) (ρ : E → ℝ)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρm : Measurable ρ) (hρ1 : ∫⁻ y, ENNReal.ofReal (ρ y) ∂μ = 1)
    {C : ℝ≥0∞} (hC : ∀ y : E, ρ y ≠ 0 → eLpNorm (fun x => u (x - y) - u x) 2 μ ≤ C) :
    eLpNorm (fun x => ∫ y, ρ y • (u (x - y) - u x) ∂μ) 2 μ ≤ C := by

  rcases eq_or_ne C ⊤ with rfl | hCtop
  · exact le_top
  have hmeas : AEMeasurable
      (Function.uncurry fun x y : E => ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ))
      (μ.prod μ) := by
    have h1 : StronglyMeasurable (Function.uncurry fun x y : E => u (x - y) - u x) :=
      (hu.comp_measurable (by fun_prop)).sub (hu.comp_measurable (by fun_prop))
    have h2 : Measurable (Function.uncurry fun x y : E => ENNReal.ofReal (ρ y)) :=
      (ENNReal.measurable_ofReal.comp hρm).comp measurable_snd
    exact (h2.mul (h1.measurable.enorm.pow_const _)).aemeasurable
  have hC2 : C ^ (2:ℝ) ≠ ⊤ := by simp [hCtop]
  have key : ∫⁻ x, ‖∫ y, ρ y • (u (x - y) - u x) ∂μ‖ₑ ^ (2:ℝ) ∂μ ≤ C ^ (2:ℝ) := by
    calc ∫⁻ x, ‖∫ y, ρ y • (u (x - y) - u x) ∂μ‖ₑ ^ (2:ℝ) ∂μ
        ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ) ∂μ ∂μ :=
          lintegral_mono fun x => enorm_mollify_sq_le u ρ hρ0 hρm hρ1 hu x
      _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ) ∂μ ∂μ :=
          lintegral_lintegral_swap hmeas
      _ ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * C ^ (2:ℝ) ∂μ := by
          refine lintegral_mono fun y => ?_
          rw [lintegral_const_mul' _ _ (by simp)]
          by_cases hy : ρ y = 0
          · simp [hy]
          · have hCy := hC y hy
            have hrw : ∫⁻ x, ‖u (x - y) - u x‖ₑ ^ (2:ℝ) ∂μ
                = (eLpNorm (fun x => u (x - y) - u x) 2 μ) ^ (2:ℝ) := by
              rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
                ← ENNReal.rpow_mul]
              norm_num
            rw [hrw]
            gcongr
      _ = C ^ (2:ℝ) := by rw [lintegral_mul_const' _ _ hC2, hρ1, one_mul]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have hstep : (∫⁻ x, ‖∫ y, ρ y • (u (x - y) - u x) ∂μ‖ₑ ^ (2:ℝ) ∂μ) ^ ((1:ℝ)/2)
      ≤ (C ^ (2:ℝ)) ^ ((1:ℝ)/2) := ENNReal.rpow_le_rpow key (by norm_num)
  have hfin : (C ^ (2:ℝ)) ^ ((1:ℝ)/2) = C := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hfin] at hstep
  simpa using hstep
