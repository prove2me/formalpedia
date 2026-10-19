-- Prove2me | solution 1 for CauchyRiemannIndex.plane_antiholomorphic_no_solution
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T11:51:50.330885+00:00
-- url     : https://prove2.me/submissions/90587832-13f2-451f-bccc-a0c3cbbad5e0

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Theorems.Thm_CauchyRiemannIndex_plane_weighted_dbar_estimate
import Theorems.Thm_CauchyRiemannIndex_exists_plane_cutoff_family
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.L2Space



namespace CauchyRiemannIndex

open MeasureTheory Filter Topology
open scoped ContDiff

theorem plane_antiholomorphic_no_solution_aux (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f)
    (h2 : MemLp f 2 volume)
    (heq : ∀ z, fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I +
      (starRingEnd ℂ) z * (starRingEnd ℂ) (f z) = 0) :
    f = 0 := by
  obtain ⟨c, M, hM0, hc⟩ := exists_plane_cutoff_family
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast le_top)
  have hfd : Differentiable ℝ f := hf1.differentiable one_ne_zero
  set A := ∫ z, ‖f z‖ ^ 2 with hA
  have hAint : Integrable fun z => ‖f z‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm h2.1).1 h2
  -- the estimate for each cutoff
  have hest : ∀ R > 0, ∫ z, ‖z‖ ^ 2 * ‖c R z * f z‖ ^ 2 ≤ (2 * M / R) ^ 2 * A := by
    intro R hR
    obtain ⟨hcC', hcS, hcR, -, hcD⟩ := hc R hR
    have hcC : ContDiff ℝ 1 (c R) := hcC'.of_le (by exact_mod_cast le_top)
    have hcd : Differentiable ℝ (c R) := hcC.differentiable one_ne_zero
    have hu : ContDiff ℝ 1 (fun z => c R z * f z) := hcC.mul hf1
    have hus : HasCompactSupport (fun z => c R z * f z) := hcS.mul_right
    have h := plane_weighted_dbar_estimate _ hu hus
    have hpt : ∀ z, fderiv ℝ (fun z => c R z * f z) z 1 +
        Complex.I * fderiv ℝ (fun z => c R z * f z) z Complex.I +
        (starRingEnd ℂ) z * (starRingEnd ℂ) (c R z * f z) =
        (fderiv ℝ (c R) z 1 + Complex.I * fderiv ℝ (c R) z Complex.I) * f z := by
      intro z
      have hprod : fderiv ℝ (fun z => c R z * f z) z =
          c R z • fderiv ℝ f z + f z • fderiv ℝ (c R) z := fderiv_mul (hcd z) (hfd z)
      rw [hprod]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        map_mul, hcR]
      linear_combination (c R z) * heq z
    simp_rw [hpt] at h
    refine h.trans ?_
    rw [hA, ← integral_const_mul]
    have hDb : ∀ z, ‖fderiv ℝ (c R) z 1 + Complex.I * fderiv ℝ (c R) z Complex.I‖ ≤ 2 * M / R := by
      intro z
      calc _ ≤ ‖fderiv ℝ (c R) z 1‖ + ‖Complex.I * fderiv ℝ (c R) z Complex.I‖ := norm_add_le _ _
        _ ≤ M / R * ‖(1 : ℂ)‖ + 1 * (M / R * ‖Complex.I‖) := by
            gcongr
            · exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hcD z)
            · rw [norm_mul]; gcongr
              · simp
              · exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hcD z)
        _ = 2 * M / R := by simp; ring
    have hcont : Continuous fun z =>
        ‖(fderiv ℝ (c R) z 1 + Complex.I * fderiv ℝ (c R) z Complex.I) * f z‖ ^ 2 :=
      ((((hcC.continuous_fderiv one_ne_zero).clm_apply continuous_const).add
        (continuous_const.mul ((hcC.continuous_fderiv one_ne_zero).clm_apply
          continuous_const))).mul hf1.continuous).norm.pow 2
    have hcs : HasCompactSupport fun z =>
        ‖(fderiv ℝ (c R) z 1 + Complex.I * fderiv ℝ (c R) z Complex.I) * f z‖ ^ 2 :=
      HasCompactSupport.intro hcS (fun z hz => by simp [fderiv_of_notMem_tsupport ℝ hz])
    refine integral_mono (hcont.integrable_of_hasCompactSupport hcs) (hAint.const_mul _)
      (fun z => ?_)
    simp only [norm_mul, mul_pow]
    gcongr
    exact hDb z
  -- vanishing away from the origin
  have hne : ∀ z₀ : ℂ, z₀ ≠ 0 → f z₀ = 0 := by
    intro z₀ hz₀
    by_contra hf0
    set h : ℂ → ℝ := fun z => ‖z‖ ^ 2 * ‖f z‖ ^ 2 with hh
    have hhc : Continuous h := (continuous_norm.pow 2).mul (hf1.continuous.norm.pow 2)
    have hpos : 0 < h z₀ := by
      have : 0 < ‖z₀‖ := norm_pos_iff.2 hz₀
      have : 0 < ‖f z₀‖ := norm_pos_iff.2 hf0
      positivity
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1
      (hhc.continuousAt.eventually (lt_mem_nhds (half_lt_self hpos)))
    set r' := min r 1 with hr'
    have hr'0 : 0 < r' := lt_min hr one_pos
    set κ := volume.real (Metric.ball z₀ r') * (h z₀ / 2) with hκ
    have hκ0 : 0 < κ := by
      have : 0 < volume.real (Metric.ball z₀ r') := ENNReal.toReal_pos
        (Metric.measure_ball_pos volume z₀ hr'0).ne' measure_ball_lt_top.ne
      positivity
    have ht : Tendsto (fun R : ℝ => (2 * M) ^ 2 * A / R ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
    obtain ⟨R, hR1, hR2⟩ := ((ht.eventually (gt_mem_nhds hκ0)).and
      (eventually_ge_atTop (‖z₀‖ + 1))).exists
    have hR : 0 < R := by linarith [norm_nonneg z₀]
    obtain ⟨hcC', hcS, -, hc1, -⟩ := hc R hR
    have hcC : ContDiff ℝ 1 (c R) := hcC'.of_le (by exact_mod_cast le_top)
    have hint : Integrable fun z => ‖z‖ ^ 2 * ‖c R z * f z‖ ^ 2 :=
      ((continuous_norm.pow 2).mul ((hcC.continuous.mul hf1.continuous).norm.pow 2)).integrable_of_hasCompactSupport
        (HasCompactSupport.intro hcS (fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]))
    have hlow : κ ≤ ∫ z, ‖z‖ ^ 2 * ‖c R z * f z‖ ^ 2 := by
      calc κ ≤ ∫ z in Metric.ball z₀ r', ‖z‖ ^ 2 * ‖c R z * f z‖ ^ 2 := by
            have := setIntegral_ge_of_const_le (μ := volume) (c := h z₀ / 2)
              (s := Metric.ball z₀ r') (f := fun z => ‖z‖ ^ 2 * ‖c R z * f z‖ ^ 2)
              measurableSet_ball measure_ball_lt_top.ne ?_ hint.integrableOn
            · simpa only [hκ, smul_eq_mul] using this
            · intro z hz
              have hzr : dist z z₀ < r := lt_of_lt_of_le hz (min_le_left _ _)
              have hzR : ‖z‖ ≤ R := by
                have : ‖z‖ ≤ ‖z₀‖ + dist z z₀ := by
                  rw [dist_eq_norm]; linarith [norm_sub_norm_le z z₀]
                have : dist z z₀ < 1 := lt_of_lt_of_le hz (min_le_right _ _)
                linarith
              rw [hc1 z hzR, one_mul]
              exact (hball hzr).le
        _ ≤ ∫ z, ‖z‖ ^ 2 * ‖c R z * f z‖ ^ 2 :=
            setIntegral_le_integral hint (Eventually.of_forall fun z => by positivity)
    have hup := hest R hR
    have : (2 * M / R) ^ 2 * A = (2 * M) ^ 2 * A / R ^ 2 := by
      field_simp
    linarith
  exact Continuous.ext_on (dense_compl_singleton 0) hf1.continuous continuous_const
    (fun z hz => hne z hz)

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f)
    (h2 : MemLp f 2 volume)
    (heq : ∀ z, fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I +
      (starRingEnd ℂ) z * (starRingEnd ℂ) (f z) = 0) :
    f = 0 :=
  plane_antiholomorphic_no_solution_aux f hf h2 heq
