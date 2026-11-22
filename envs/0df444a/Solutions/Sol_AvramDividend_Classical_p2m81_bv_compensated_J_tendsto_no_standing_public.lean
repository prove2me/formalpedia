-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_compensated_J_tendsto_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T14:15:31.986882+00:00
-- url     : https://prove2.me/submissions/fcbdfab3-098e-4b97-9f5e-5f6b20128631

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_small_negative_jump_deficit_integral_of_integrable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option autoImplicit false

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    Tendsto (fun n : ℕ => ∫ y : ℝ,
      (Real.exp (((n : ℝ) + 1) * y) - 1 - ((n : ℝ) + 1) * y) / ((n : ℝ) + 1)
        ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))) atTop
      (nhds (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0)))) := by
  let μ := X.ν.restrict (Ioo (-1 : ℝ) 0)
  let G (θ y : ℝ) := (1 - Real.exp (θ * y)) / θ
  let A := ∫ y : ℝ, |y| ∂μ
  have hmom : Integrable (fun y : ℝ => -y) μ := bv_small_negative_first_moment_integrable X hBV
  have hA : (∫ y : ℝ, -y ∂μ) = A := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo (μ := X.ν)] with y hy
    exact (abs_of_neg hy.2).symm
  have hGi (θ : ℝ) (hθ : 0 < θ) : Integrable (G θ) μ := by
    have hcont : Continuous (G θ) := by dsimp [G]; fun_prop
    refine hmom.mono' hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo (μ := X.ν)] with y hy
    have hexp : Real.exp (θ * y) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hθ.le hy.2.le)
    have hnonneg : 0 ≤ G θ y := div_nonneg (sub_nonneg.mpr hexp) hθ.le
    rw [Real.norm_of_nonneg hnonneg]
    exact (div_le_iff₀ hθ).2 (by linarith [Real.add_one_le_exp (θ * y)])
  have harg : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa [Function.comp_def] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat 1)
  have hdeficit : Tendsto (fun n : ℕ => ∫ y : ℝ, G ((n : ℝ) + 1) y ∂μ) atTop (nhds 0) :=
    (small_negative_jump_deficit_integral_of_integrable X.ν hmom).comp harg
  have hlim := (tendsto_const_nhds (x := A)).sub hdeficit
  rw [sub_zero] at hlim
  refine hlim.congr fun n => ?_
  let θ : ℝ := (n : ℝ) + 1
  have hθ : 0 < θ := by dsimp [θ]; positivity
  change A - (∫ y : ℝ, G θ y ∂μ) = ∫ y : ℝ, (Real.exp (θ * y) - 1 - θ * y) / θ ∂μ
  rw [← hA, ← integral_sub hmom (hGi θ hθ)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp [G]
    field_simp [hθ.ne']
    ring
