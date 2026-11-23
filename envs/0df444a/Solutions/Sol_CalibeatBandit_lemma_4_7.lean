-- Prove2me | solution 1 for CalibeatBandit.lemma_4_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T18:47:31.768622+00:00
-- url     : https://prove2.me/submissions/d23e66e1-74e4-4a73-b2b8-646261bd597b

import Mathlib
import Definitions.Def_CalibeatBandit_lower_bound_models
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_hard_tree_environment
import Definitions.Def_CalibeatBandit_hard_tree_analysis

section

set_option autoImplicit false

open Filter MeasureTheory Set InformationTheory
open scoped Interval ENNReal

namespace CalibeatBandit

theorem bonusTransform_deriv (η z : ℝ) :
    HasDerivAt (bonusTransform η) (1 + η * (1 - 2 * z)) z := by
  unfold bonusTransform
  have h := (hasDerivAt_id z).add
    (((hasDerivAt_id z).const_mul η).mul ((hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_id z)))
  change HasDerivAt (fun x : ℝ => x + η * x * (1 - x)) _ z at h
  convert h using 1
  simp only [Pi.sub_apply, id_eq]
  ring

theorem bonusTransform_deriv_pos {η z : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η < 1)
    (hz : z ∈ Icc (0 : ℝ) 1) : 0 < 1 + η * (1 - 2 * z) := by
  nlinarith [mul_nonneg hη₀ (sub_nonneg.mpr hz.2)]

theorem bonusTransform_strictMonoOn {η : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η < 1) :
    StrictMonoOn (bonusTransform η) (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have h : 0 < 1 + η * (1 - x - y) := by
    nlinarith [mul_nonneg hη₀ (sub_nonneg.mpr hx.2), mul_nonneg hη₀ (sub_nonneg.mpr hy.2)]
  calc
    bonusTransform η x < bonusTransform η x + (y - x) * (1 + η * (1 - x - y)) :=
      lt_add_of_pos_right _ (mul_pos (sub_pos.mpr hxy) h)
    _ = bonusTransform η y := by unfold bonusTransform; ring

/-- The integral inequality after the change of variables in Appendix D.2.
The derivative is positive throughout the integration interval. -/
theorem bonus_log_jacobian_integral_le {η : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η < 1) :
    (∫ z in (0 : ℝ)..1, (1 + η * (1 - 2 * z)) * Real.log (1 + η * (1 - 2 * z)))
      ≤ η ^ 2 / 3 := by
  let J (z : ℝ) := 1 + η * (1 - 2 * z)
  let F (z : ℝ) := J z * Real.log (J z)
  let G (z : ℝ) := (η + η ^ 2) + (-(2 * η) - 4 * η ^ 2) * z + (4 * η ^ 2) * z ^ 2
  have hJ : Continuous J := by unfold J; fun_prop
  have hF : ContinuousOn F (Icc (0 : ℝ) 1) := by
    exact hJ.continuousOn.mul (hJ.continuousOn.log fun z hz => (bonusTransform_deriv_pos hη₀ hη₁ hz).ne')
  have hG : Continuous G := by unfold G; fun_prop
  have hle (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : F z ≤ G z := by
    have hpos : 0 < J z := bonusTransform_deriv_pos hη₀ hη₁ hz
    have hl := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hpos) hpos.le
    calc
      F z ≤ J z * (J z - 1) := hl
      _ = G z := by unfold J G; ring
  have hbound : (∫ z in (0 : ℝ)..1, F z) ≤ ∫ z in (0 : ℝ)..1, G z := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply ContinuousOn.intervalIntegrable
      simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hF
    · exact hG.intervalIntegrable _ _
    · exact hle
  have hg : (∫ z in (0 : ℝ)..1, G z) = η ^ 2 / 3 := by
    have ha : IntervalIntegrable (fun _ : ℝ => η + η ^ 2) volume 0 1 := by
      exact continuous_const.intervalIntegrable _ _
    have hb : IntervalIntegrable (fun z : ℝ => (-(2 * η) - 4 * η ^ 2) * z) volume 0 1 := by
      exact (continuous_const.mul continuous_id).intervalIntegrable _ _
    have hc : IntervalIntegrable (fun z : ℝ => (4 * η ^ 2) * z ^ 2) volume 0 1 := by
      exact (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
    unfold G
    rw [intervalIntegral.integral_add (ha.add hb) hc, intervalIntegral.integral_add ha hb,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_id,
      integral_pow, intervalIntegral.integral_const]
    norm_num
    ring
  exact hbound.trans_eq hg

/-- Lemma 4.7. The uniform law on the unit interval has divergence at most
η²/3 relative to its pushforward under the bonus transform. -/
theorem lemma_4_7 {η : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η < 1) :
    let Q := volume.restrict (Icc (0 : ℝ) 1)
    klDiv Q (Q.map (bonusTransform η)) ≤ ENNReal.ofReal (η ^ 2 / 3) := by
  intro Q
  let J (z : ℝ) := 1 + η * (1 - 2 * z)
  let g (z : ℝ) := ENNReal.ofReal (J z)
  let h := bonusTransform η
  let Q' := Q.withDensity g
  have hmJ : Continuous J := by unfold J; fun_prop
  have hmg : Measurable g := hmJ.measurable.ennreal_ofReal
  have hmh : Continuous h := by unfold h bonusTransform; fun_prop
  have hmono : StrictMonoOn h (Icc (0 : ℝ) 1) := bonusTransform_strictMonoOn hη₀ hη₁
  have hpos (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : 0 < J x :=
    bonusTransform_deriv_pos hη₀ hη₁ hx
  have himage : h '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
    rw [hmh.continuousOn.image_Icc_of_monotoneOn (show (0 : ℝ) ≤ 1 by norm_num)
      (StrictMonoOn.monotoneOn hmono)]
    simp [h, bonusTransform]
  have hmap : Q'.map h = Q := by
    ext s hs
    rw [Measure.map_apply hmh.measurable hs, withDensity_apply _ (hmh.measurable hs)]
    have hchange := lintegral_image_eq_lintegral_abs_deriv_mul
      (f := h) (f' := J) measurableSet_Icc
      (fun x _ => (bonusTransform_deriv η x).hasDerivWithinAt) hmono.injOn
      (s.indicator fun _ => (1 : ℝ≥0∞))
    rw [himage, lintegral_indicator hs] at hchange
    simp only [lintegral_const, one_mul, Measure.restrict_apply_univ] at hchange
    change _ = (volume.restrict (Icc (0 : ℝ) 1)) s
    rw [hchange, ← lintegral_indicator (hmh.measurable hs)]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with x hx
    by_cases hx' : h x ∈ s <;>
      simp [g, hx', abs_of_pos (hpos x hx)]
  have hac : Q' ≪ Q := withDensity_absolutelyContinuous _ _
  have hll : llr Q' Q =ᵐ[Q] fun z => Real.log (J z) := by
    filter_upwards [Measure.rnDeriv_withDensity Q hmg,
      ae_restrict_mem (μ := volume) measurableSet_Icc] with z hz hmem
    change Real.log ((Q'.rnDeriv Q z).toReal) = Real.log (J z)
    change Q'.rnDeriv Q z = g z at hz
    rw [hz, ENNReal.toReal_ofReal (hpos z hmem).le]
  have hlog : ContinuousOn (fun z => Real.log (J z)) (Icc (0 : ℝ) 1) :=
    hmJ.continuousOn.log fun z hz => (hpos z hz).ne'
  have hprod : Integrable (fun z => (g z).toReal • Real.log (J z)) Q := by
    have hc := hmJ.continuousOn.mul hlog
    apply (hc.integrableOn_compact isCompact_Icc).congr
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with z hz
    simp [g, ENNReal.toReal_ofReal (hpos z hz).le, smul_eq_mul]
  have hgfinite : ∀ᵐ z ∂Q, g z < ⊤ := ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hli' : Integrable (fun z => Real.log (J z)) Q' :=
    (integrable_withDensity_iff_integrable_smul' hmg hgfinite).mpr hprod
  have hll' : llr Q' Q =ᵐ[Q'] fun z => Real.log (J z) := hll.filter_mono hac.ae_le
  have hli : Integrable (llr Q' Q) Q' := hli'.congr hll'.symm
  have hmass : Q' univ = Q univ := by
    rw [← hmap, Measure.map_apply hmh.measurable MeasurableSet.univ, preimage_univ]
  let : IsFiniteMeasure Q' := ⟨hmass ▸ measure_lt_top Q univ⟩
  have hi : (∫ z, llr Q' Q z ∂Q') ≤ η ^ 2 / 3 := by
    rw [integral_congr_ae hll',
      integral_withDensity_eq_integral_toReal_smul hmg hgfinite]
    have he : (∫ z, (g z).toReal • Real.log (J z) ∂Q) =
        ∫ z in (0 : ℝ)..1, J z * Real.log (J z) := by
      rw [intervalIntegral.integral_of_le (by norm_num), restrict_Ioc_eq_restrict_Icc]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with z hz
      simp [g, ENNReal.toReal_ofReal (hpos z hz).le, smul_eq_mul]
    rw [he]
    exact bonus_log_jacobian_integral_le hη₀ hη₁
  calc
    klDiv Q (Q.map h) ≤ klDiv Q' Q := hmap ▸ klDiv_map_le Q' Q hmh.measurable
    _ ≤ _ := by
      rw [klDiv_of_ac_of_integrable hac hli, show Q.real univ = Q'.real univ by
        simp only [measureReal_def, hmass], add_sub_cancel_right]
      exact ENNReal.ofReal_le_ofReal hi

end CalibeatBandit

end

theorem solution : type_of% @CalibeatBandit.lemma_4_7 := @CalibeatBandit.lemma_4_7
