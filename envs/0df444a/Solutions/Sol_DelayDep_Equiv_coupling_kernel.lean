-- Prove2me | solution 1 for DelayDep.Equiv.coupling_kernel
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T09:28:24.373137+00:00
-- url     : https://prove2.me/submissions/ec8fd9d8-7599-4063-b68d-f7c0dc38928e

import Mathlib
import Definitions.Def_DelayDep_Equiv_Model
import Definitions.Def_DelayDep_Equiv_CouplingKernel

namespace DDK
open MeasureTheory DelayDep.Equiv

lemma ofReal_int (ν : Measure ℝ) {h : ℝ → ℝ} (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x)
    (hfin : ∫⁻ x, ENNReal.ofReal (h x) ∂ν ≠ ⊤) :
    ENNReal.ofReal (∫ x, h x ∂ν) = ∫⁻ x, ENNReal.ofReal (h x) ∂ν := by
  apply ofReal_integral_eq_lintegral_ofReal _ (Filter.Eventually.of_forall h0)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall h0)]; exact hfin.lt_top

end DDK

open MeasureTheory DelayDep.Equiv DDK in
theorem solution (f : ℝ → ℝ → ℝ) (hf : IsJointPdf f) (z : ℝ) (hz : 0 ≤ z)
    (htail : 0 < tailT f z) (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) :
    ∫⁻ p, couplingMeasure f z p A ∂((pdfLaw (fTex f)).prod (pdfLaw (fun x => psiEn f x z))) =
      jointLaw f A := by
  obtain ⟨hfm, hf0, hf1⟩ := hf
  set μ : Measure ℝ := volume.restrict (Set.Ici 0) with hμ
  set ν : Measure ℝ := volume.restrict (Set.Ioi z) with hν
  set F : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (f p.1 p.2) with hF
  have hFm : Measurable F := ENNReal.measurable_ofReal.comp hfm
  have hprod : volume.restrict (Set.Ici (0:ℝ) ×ˢ Set.Ici (0:ℝ)) = μ.prod μ := by
    rw [hμ, Measure.prod_restrict, ← Measure.volume_eq_prod]
  have htot : ∫⁻ y, ∫⁻ x, F (x, y) ∂μ ∂μ = 1 := by
    rw [← lintegral_prod_symm _ hFm.aemeasurable, ← hprod]; exact hf1
  have hνμ : ν ≤ μ := Measure.restrict_mono (fun x hx => le_trans hz (le_of_lt hx)) le_rfl
  have hμν : μ.restrict (Set.Ioi z) = ν := by
    rw [hμ, hν, Measure.restrict_restrict measurableSet_Ioi,
      Set.inter_eq_left.mpr (show Set.Ioi z ⊆ Set.Ici 0 from fun x hx => le_trans hz (le_of_lt hx))]
  -- marginal facts
  set fT := fTex f with hfT
  have hTm : Measurable fT := (hfm.stronglyMeasurable.integral_prod_left (μ := μ)).measurable
  have hT0 : ∀ y, 0 ≤ fT y := fun y => integral_nonneg (fun x => hf0 x y)
  have hae : ∀ᵐ y ∂μ, ENNReal.ofReal (fT y) = ∫⁻ x, F (x, y) ∂μ := by
    have hlt := ae_lt_top (hFm.lintegral_prod_left' (μ := μ)) (by rw [htot]; exact ENNReal.one_ne_top)
    filter_upwards [hlt] with y hy
    exact ofReal_int μ (hfm.comp (measurable_id.prodMk measurable_const)) (fun x => hf0 x y) hy.ne
  have hpdfT : ∫⁻ y, ENNReal.ofReal (fT y) ∂μ = 1 := by rw [lintegral_congr_ae hae, htot]
  -- D and psi
  set D : ℝ → ℝ := fun s => ∫ y, f s y ∂ν with hD
  have hDm : Measurable D := hfm.stronglyMeasurable.integral_prod_right'.measurable
  have hD0 : ∀ s, 0 ≤ D s := fun s => integral_nonneg (fun y => hf0 s y)
  have hfin2 : ∫⁻ x, ∫⁻ y, F (x, y) ∂ν ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ x, ∫⁻ y, F (x, y) ∂μ ∂μ) ?_ ?_
    · rw [lintegral_lintegral_swap (f := fun x y => F (x, y)) hFm.aemeasurable, htot]
      exact ENNReal.one_ne_top
    · exact lintegral_mono (fun x => lintegral_mono' hνμ le_rfl)
  have haeD : ∀ᵐ s ∂μ, ENNReal.ofReal (D s) = ∫⁻ y, F (s, y) ∂ν := by
    have hlt := ae_lt_top (hFm.lintegral_prod_right' (ν := ν)) hfin2
    filter_upwards [hlt] with x hx
    exact ofReal_int ν (hfm.comp (measurable_const.prodMk measurable_id)) (fun y => hf0 x y) hx.ne
  set t := tailT f z with ht
  have hB : ENNReal.ofReal t = ∫⁻ y, ENNReal.ofReal (fT y) ∂ν := by
    have hfinT : ∫⁻ y, ENNReal.ofReal (fT y) ∂ν ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ y, ENNReal.ofReal (fT y) ∂μ) ?_ (lintegral_mono' hνμ le_rfl)
      rw [hpdfT]; exact ENNReal.one_ne_top
    exact ofReal_int ν hTm hT0 hfinT
  have htpos : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr htail).ne'
  have htfin : ENNReal.ofReal t ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpsi : ∀ s, psiEn f s z = D s / t := fun s => rfl
  have hDtot : ∫⁻ s, ENNReal.ofReal (D s) ∂μ = ENNReal.ofReal t := by
    rw [lintegral_congr_ae haeD, hB, lintegral_congr_ae (ae_mono hνμ hae)]
    exact lintegral_lintegral_swap (f := fun x y => F (x, y)) hFm.aemeasurable
  have hpsitot : ∫⁻ s, ENNReal.ofReal (psiEn f s z) ∂μ = 1 := by
    simp_rw [hpsi, ENNReal.ofReal_div_of_pos htail, div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr htpos), hDtot]
    exact ENNReal.mul_inv_cancel htpos htfin
  -- the kernel
  set F2 : ℝ × ℝ → ENNReal := fun p => A.indicator (fun _ => (1:ENNReal)) p * F p with hF2
  have hF2m : Measurable F2 := (measurable_const.indicator hA).mul hFm
  set G1 : ℝ × ℝ → ENNReal := fun p =>
    A.indicator (fun _ => (1:ENNReal)) p * ENNReal.ofReal (f p.1 p.2 / fT p.2) with hG1
  have hG1m : Measurable G1 :=
    (measurable_const.indicator hA).mul (ENNReal.measurable_ofReal.comp (hfm.div (hTm.comp measurable_snd)))
  set G2 : ℝ × ℝ → ENNReal := fun p =>
    A.indicator (fun _ => (1:ENNReal)) p * ENNReal.ofReal (f p.1 p.2 / D p.1) with hG2
  have hG2m : Measurable G2 :=
    (measurable_const.indicator hA).mul (ENNReal.measurable_ofReal.comp (hfm.div (hDm.comp measurable_fst)))
  have hind : ∀ (g : ℝ → ENNReal) (S : Set ℝ) (m : Measure ℝ), MeasurableSet S →
      ∫⁻ x in S, g x ∂m = ∫⁻ x, S.indicator (fun _ => (1:ENNReal)) x * g x ∂m := by
    intro g S m hS
    rw [← lintegral_indicator hS]
    congr 1; funext x
    by_cases hx : x ∈ S <;> simp [hx]
  have hK : ∀ p : ℝ × ℝ, couplingMeasure f z p A =
      if p.1 ≤ z then ∫⁻ x, G1 (x, p.1) ∂μ else ∫⁻ y, G2 (p.2, y) ∂ν := by
    intro p
    unfold couplingMeasure
    split_ifs with h
    · rw [Measure.map_apply measurable_prodMk_right hA, pdfLaw,
        withDensity_apply _ (measurable_prodMk_right hA)]
      rw [hind _ _ _ (measurable_prodMk_right hA)]
      rfl
    · rw [Measure.map_apply measurable_prodMk_left hA,
        withDensity_apply _ (measurable_prodMk_left hA)]
      rw [hind _ _ _ (measurable_prodMk_left hA)]
      rfl
  have hK1m : Measurable (fun s : ℝ => ∫⁻ x, G1 (x, s) ∂μ) := hG1m.lintegral_prod_left'
  have hK2m : Measurable (fun s : ℝ => ∫⁻ y, G2 (s, y) ∂ν) := hG2m.lintegral_prod_right'
  set Kf : ℝ × ℝ → ENNReal := fun p => couplingMeasure f z p A with hKf
  have hKf : Kf = fun p => if p.1 ≤ z then ∫⁻ x, G1 (x, p.1) ∂μ else ∫⁻ y, G2 (p.2, y) ∂ν := by
    funext p; exact hK p
  have hKm : Measurable Kf := by
    rw [hKf]
    exact Measurable.ite (measurableSet_le measurable_fst measurable_const)
      (hK1m.comp measurable_fst) (hK2m.comp measurable_snd)
  set a : ℝ → ENNReal := fun y => ENNReal.ofReal (fT y) with ha
  set b : ℝ → ENNReal := fun s => ENNReal.ofReal (psiEn f s z) with hb
  have ham : Measurable a := ENNReal.measurable_ofReal.comp hTm
  have hbm : Measurable b := ENNReal.measurable_ofReal.comp (hDm.div_const _)
  haveI : SFinite (pdfLaw fT) := by unfold pdfLaw; infer_instance
  haveI : SFinite (pdfLaw (fun x => psiEn f x z)) := by unfold pdfLaw; infer_instance
  -- LHS as an iterated integral
  have hL1 : ∫⁻ p, Kf p ∂((pdfLaw fT).prod (pdfLaw (fun x => psiEn f x z))) =
      ∫⁻ y, a y * ∫⁻ s, b s * Kf (y, s) ∂μ ∂μ := by
    rw [lintegral_prod _ hKm.aemeasurable]
    unfold pdfLaw
    rw [lintegral_withDensity_eq_lintegral_mul _ ham (hKm.lintegral_prod_right' )]
    congr 1; funext y
    simp only [Pi.mul_apply]
    congr 1
    exact lintegral_withDensity_eq_lintegral_mul _ hbm (hKm.comp measurable_prodMk_left)
  -- inner integral
  set C := ∫⁻ s, b s * ∫⁻ y, G2 (s, y) ∂ν ∂μ with hC
  have hinner : ∀ y, ∫⁻ s, b s * Kf (y, s) ∂μ =
      if y ≤ z then ∫⁻ x, G1 (x, y) ∂μ else C := by
    intro y
    rw [hKf]
    split_ifs with h
    · simp only [h, if_true]
      rw [lintegral_mul_const _ hbm, hpsitot, one_mul]
    · simp only [h, if_false]; rfl
  have hC2 : ENNReal.ofReal t * C = ∫⁻ s, ∫⁻ y, F2 (s, y) ∂ν ∂μ := by
    have : ∀ᵐ s ∂μ, b s * ∫⁻ y, G2 (s, y) ∂ν = (ENNReal.ofReal t)⁻¹ * ∫⁻ y, F2 (s, y) ∂ν := by
      filter_upwards [haeD] with s hs
      by_cases hDs : D s = 0
      · have h0 : ∫⁻ y, F (s, y) ∂ν = 0 := by rw [← hs, hDs, ENNReal.ofReal_zero]
        have h0' : ∫⁻ y, F2 (s, y) ∂ν = 0 := by
          refine le_antisymm (le_of_le_of_eq (lintegral_mono fun y => ?_) h0) bot_le
          simp only [hF2]
          by_cases hy : (s, y) ∈ A <;> simp [hy]
        simp [hb, hpsi, hDs, h0']
      · have hDpos : 0 < D s := lt_of_le_of_ne (hD0 s) (Ne.symm hDs)
        rw [← lintegral_const_mul _ (show Measurable (fun y => G2 (s, y)) from
            hG2m.comp measurable_prodMk_left),
          ← lintegral_const_mul _ (show Measurable (fun y => F2 (s, y)) from
            hF2m.comp measurable_prodMk_left)]
        congr 1; funext y
        simp only [hb, hG2, hF2, hF, hpsi]
        rw [mul_left_comm, ← ENNReal.ofReal_mul (div_nonneg (hD0 s) htail.le)]
        rw [show D s / t * (f s y / D s) = f s y / t by field_simp]
        rw [ENNReal.ofReal_div_of_pos htail, div_eq_mul_inv]; ring
    rw [hC, lintegral_congr_ae this,
      lintegral_const_mul _ (hF2m.lintegral_prod_right' (ν := ν)), ← mul_assoc,
      ENNReal.mul_inv_cancel htpos htfin, one_mul]
  have hK1 : ∀ᵐ y ∂μ, a y * ∫⁻ x, G1 (x, y) ∂μ = ∫⁻ x, F2 (x, y) ∂μ := by
    filter_upwards [hae] with y hy
    by_cases hTy : fT y = 0
    · have h0 : ∫⁻ x, F (x, y) ∂μ = 0 := by rw [← hy, hTy, ENNReal.ofReal_zero]
      have h0' : ∫⁻ x, F2 (x, y) ∂μ = 0 := by
        refine le_antisymm (le_of_le_of_eq (lintegral_mono fun x => ?_) h0) bot_le
        simp only [hF2]
        by_cases hx : (x, y) ∈ A <;> simp [hx]
      simp [ha, hTy, h0']
    · have hTpos : 0 < fT y := lt_of_le_of_ne (hT0 y) (Ne.symm hTy)
      rw [← lintegral_const_mul _ (show Measurable (fun x => G1 (x, y)) from
          hG1m.comp measurable_prodMk_right)]
      congr 1; funext x
      simp only [ha, hG1, hF2, hF]
      rw [mul_left_comm, ← ENNReal.ofReal_mul (hT0 y)]
      rw [show fT y * (f x y / fT y) = f x y by field_simp]
  have hsplit : ∀ g : ℝ → ENNReal,
      ∫⁻ y, g y ∂μ = ∫⁻ y in Set.Iic z, g y ∂μ + ∫⁻ y in Set.Ioi z, g y ∂μ := fun g => by
    rw [← lintegral_add_measure, ← Set.compl_Iic, Measure.restrict_add_restrict_compl measurableSet_Iic]
  -- assemble the left side
  have hLHS : ∫⁻ p, Kf p ∂((pdfLaw fT).prod (pdfLaw (fun x => psiEn f x z))) =
      ∫⁻ y in Set.Iic z, ∫⁻ x, F2 (x, y) ∂μ ∂μ + ∫⁻ s, ∫⁻ y, F2 (s, y) ∂ν ∂μ := by
    rw [hL1]
    simp_rw [hinner]
    rw [hsplit]
    congr 1
    · apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Iic, ae_restrict_of_ae hK1] with y hy hy2
      rw [if_pos (show y ≤ z from hy), hy2]
    · rw [← hC2]
      have : ∀ y ∈ Set.Ioi z, a y * (if y ≤ z then ∫⁻ x, G1 (x, y) ∂μ else C) = a y * C := by
        intro y hy; rw [if_neg (not_le.mpr hy)]
      rw [setLIntegral_congr_fun measurableSet_Ioi this, lintegral_mul_const _ ham, hμν, ← hB]
  -- the right side
  have hRHS : jointLaw f A =
      ∫⁻ y in Set.Iic z, ∫⁻ x, F2 (x, y) ∂μ ∂μ + ∫⁻ s, ∫⁻ y, F2 (s, y) ∂ν ∂μ := by
    unfold jointLaw
    rw [withDensity_apply _ hA, hprod]
    have e1 : ∫⁻ p in A, ENNReal.ofReal (f p.1 p.2) ∂(μ.prod μ) = ∫⁻ p, F2 p ∂(μ.prod μ) := by
      rw [← lintegral_indicator hA]
      congr 1; funext p
      by_cases hp : p ∈ A <;> simp [hF2, hF, hp]
    rw [e1, lintegral_prod _ hF2m.aemeasurable]
    have e2 : ∀ x, ∫⁻ y, F2 (x, y) ∂μ = ∫⁻ y in Set.Iic z, F2 (x, y) ∂μ + ∫⁻ y, F2 (x, y) ∂ν := by
      intro x
      rw [hsplit, hμν]
    simp_rw [e2]
    rw [lintegral_add_left (hF2m.lintegral_prod_right' (ν := μ.restrict (Set.Iic z)))]
    congr 1
    exact lintegral_lintegral_swap (f := fun x y => F2 (x, y)) hF2m.aemeasurable
  rw [hLHS, hRHS]
