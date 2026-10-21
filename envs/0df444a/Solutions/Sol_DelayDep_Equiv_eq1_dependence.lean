-- Prove2me | solution 1 for DelayDep.Equiv.eq1_dependence
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T09:16:29.059346+00:00
-- url     : https://prove2.me/submissions/ea4edd68-c608-471f-8247-ece9bd00a2ae

import Mathlib
import Definitions.Def_DelayDep_Equiv_Model

namespace DDE
open MeasureTheory DelayDep.Equiv

lemma ofReal_int (ν : Measure ℝ) {h : ℝ → ℝ} (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x)
    (hfin : ∫⁻ x, ENNReal.ofReal (h x) ∂ν ≠ ⊤) :
    ENNReal.ofReal (∫ x, h x ∂ν) = ∫⁻ x, ENNReal.ofReal (h x) ∂ν := by
  apply ofReal_integral_eq_lintegral_ofReal _ (Filter.Eventually.of_forall h0)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall h0)]; exact hfin.lt_top

end DDE

open MeasureTheory DelayDep.Equiv DDE in
theorem solution (f : ℝ → ℝ → ℝ) (hf : IsJointPdf f) :
    IsPdf (fTex f) ∧
      ∀ z : ℝ, 0 ≤ z → 0 < tailT f z → IsPdf (fun x => psiEn f x z) := by
  obtain ⟨hfm, hf0, hf1⟩ := hf
  set μ : Measure ℝ := volume.restrict (Set.Ici 0) with hμ
  set F : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (f p.1 p.2) with hF
  have hFm : Measurable F := ENNReal.measurable_ofReal.comp hfm
  have hprod : volume.restrict (Set.Ici (0:ℝ) ×ˢ Set.Ici (0:ℝ)) = μ.prod μ := by
    rw [hμ, Measure.prod_restrict, ← Measure.volume_eq_prod]
  have htot : ∫⁻ y, ∫⁻ x, F (x, y) ∂μ ∂μ = 1 := by
    rw [← lintegral_prod_symm _ hFm.aemeasurable, ← hprod]; exact hf1
  have hsec_meas : ∀ y, Measurable (fun x => f x y) := fun y =>
    hfm.comp (measurable_id.prodMk measurable_const)
  -- marginal
  have hTm : Measurable (fTex f) := by
    have := (hfm.stronglyMeasurable).integral_prod_left (μ := μ)
    exact this.measurable
  have hT0 : ∀ y, 0 ≤ fTex f y := fun y => integral_nonneg (fun x => hf0 x y)
  have hinner_m : Measurable (fun y => ∫⁻ x, F (x, y) ∂μ) := hFm.lintegral_prod_left'
  have hae : ∀ᵐ y ∂μ, ENNReal.ofReal (fTex f y) = ∫⁻ x, F (x, y) ∂μ := by
    have hlt := ae_lt_top hinner_m (by rw [htot]; exact ENNReal.one_ne_top)
    filter_upwards [hlt] with y hy
    exact ofReal_int μ (hsec_meas y) (fun x => hf0 x y) hy.ne
  have hpdfT : IsPdf (fTex f) := by
    refine ⟨hTm, hT0, ?_⟩
    show ∫⁻ y, ENNReal.ofReal (fTex f y) ∂μ = 1
    rw [lintegral_congr_ae hae, htot]
  refine ⟨hpdfT, ?_⟩
  intro z hz htail
  set ν : Measure ℝ := volume.restrict (Set.Ioi z) with hν
  have hνμ : ν ≤ μ := Measure.restrict_mono (fun x hx => le_trans hz (le_of_lt hx)) le_rfl
  set g : ℝ → ℝ := fun x => ∫ y, f x y ∂ν with hg
  have hgm : Measurable g := (hfm.stronglyMeasurable).integral_prod_right'.measurable
  have hg0 : ∀ x, 0 ≤ g x := fun x => integral_nonneg (fun y => hf0 x y)
  have hpsi : (fun x => psiEn f x z) = fun x => g x / tailT f z := rfl
  have hfin2 : ∫⁻ x, ∫⁻ y, F (x, y) ∂ν ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ x, ∫⁻ y, F (x, y) ∂μ ∂μ) ?_ ?_
    · rw [lintegral_lintegral_swap hFm.aemeasurable, htot]; exact ENNReal.one_ne_top
    · exact lintegral_mono (fun x => lintegral_mono' hνμ le_rfl)
  have hA : ∫⁻ x, ENNReal.ofReal (g x) ∂μ = ∫⁻ x, ∫⁻ y, F (x, y) ∂ν ∂μ := by
    apply lintegral_congr_ae
    have hlt := ae_lt_top (hFm.lintegral_prod_right' (ν := ν)) hfin2
    filter_upwards [hlt] with x hx
    exact ofReal_int ν (hfm.comp (measurable_const.prodMk measurable_id)) (fun y => hf0 x y) hx.ne
  have hB : ENNReal.ofReal (tailT f z) = ∫⁻ y, ∫⁻ x, F (x, y) ∂μ ∂ν := by
    have hfinT : ∫⁻ y, ENNReal.ofReal (fTex f y) ∂ν ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ y, ENNReal.ofReal (fTex f y) ∂μ) ?_ (lintegral_mono' hνμ le_rfl)
      rw [hpdfT.2.2]; exact ENNReal.one_ne_top
    show ENNReal.ofReal (∫ y, fTex f y ∂ν) = _
    rw [ofReal_int ν hTm hT0 hfinT]
    exact lintegral_congr_ae (ae_mono hνμ hae)
  have hAB : ∫⁻ x, ENNReal.ofReal (g x) ∂μ = ENNReal.ofReal (tailT f z) := by
    rw [hA, hB, lintegral_lintegral_swap (f := fun x y => F (x, y)) hFm.aemeasurable]
  refine ⟨hgm.div_const _, fun x => div_nonneg (hg0 x) htail.le, ?_⟩
  show ∫⁻ x, ENNReal.ofReal (g x / tailT f z) ∂μ = 1
  simp_rw [ENNReal.ofReal_div_of_pos htail, div_eq_mul_inv]
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr htail).ne'), hAB]
  exact ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr htail).ne' ENNReal.ofReal_ne_top
