-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.needs.thmPInt_of_covolume_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:35:41.653979+00:00
-- url     : https://prove2.me/submissions/77b5a755-3f0f-48dd-a6cb-ffc3d5087c82

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_needs_ptSize_loc
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_needs_Qm_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_needs_Qm_mp
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_needs_integrable_of_decay
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt Filter Topology MeasureTheory NumberField
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.needs
noncomputable section
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.JCx1.needs
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
    (dl : ℕ → Fin S.f → ℝ) (hpos : C.ThmPPos S)
    (hcov : ∀ i, 1 ≤ i → i ≤ S.G.r + 1 →
      ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) ≠ 0)
    (hprod : ∀ i, 1 ≤ i → i ≤ S.G.r + 1 →
      ∏ v, dl i v = ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1))
    (hpl : ∀ v, JC.ThmPIntPlace S v fun i => dl i v) : C.ThmPInt S := by
  intro ε hε i hi1 hi2 w Y hY κ hκ
  have H : ∀ (v : Fin S.f) (h h' : Y), ∃ φ : ℂ → ℂ, Continuous φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = S.gramLoc v ε i (w.1 v) (C.loc (S.σ v) h ++ [(1, c)])
        (C.loc (S.σ v) h' ++ [(1, c)])) ∧
      (∃ Cφ : ℝ, ∀ c : ℂ, ‖φ c‖ ≤ Cφ * ((1 + ‖c‖) ^ 3)⁻¹) ∧
      ∫ c : ℂ, φ c = (dl i v : ℂ) * S.gramLoc v ε (i - 1) (w.1 v) (C.loc (S.σ v) h) (C.loc (S.σ v) h') := by
    intro v h h'
    exact hpl v ε hε i hi1 hi2 w _ _ (by rw [ptSize_loc]; exact hY h h.2)
      (by rw [ptSize_loc]; exact hY h' h'.2)
  choose φ hφc hφe hφb hφi using H
  choose Cφ hCφ using hφb
  set sz : ℂ := (C.Word.size S.P w.1 : ℂ) with hsz
  set Φ : (Fin S.f → ℂ) → ℂ := fun y => (∑ h : Y, ∑ h' : Y, κ h h' * ∏ v, φ v h h' (y v)) / sz with hΦ
  have hΦc : Continuous Φ := by
    apply Continuous.div_const
    exact continuous_finsetSum _ fun h _ => continuous_finsetSum _ fun h' _ =>
      continuous_const.mul (continuous_finsetProd _ fun v _ => (hφc v h h').comp (continuous_apply v))
  have hN1 : ∀ c : J.CV E, (∀ v, c (S.pl v) ≠ 0) → S.N1 ε i w.1 Y κ c = Φ (Qm S c) := by
    intro c hc
    simp only [C.HidaSetting.N1, hΦ, Qm_apply]
    congr 1
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun h' _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hφe v h h' _ (hc v)]
  have hQc : Continuous (Qm S) := by
    have : Qm S = fun c v => c (S.pl v) := funext fun c => funext fun v => Qm_apply S c v
    rw [this]
    exact continuous_pi fun v => (EuclideanSpace.proj (𝕜 := ℂ) (S.pl v)).continuous
  refine ⟨⟨fun c => Φ (Qm S c), hΦc.comp hQc, fun c hc => (hN1 c hc).symm,
    (∑ h : Y, ∑ h' : Y, ‖κ h h'‖ * ∏ v, Cφ v h h') / ‖sz‖, fun c => ?_⟩, ?_⟩
  ·
    simp only [hΦ, Qm_apply, norm_div]
    rw [div_mul_eq_mul_div]
    gcongr
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h' _ => ?_)
    rw [norm_mul, norm_prod, mul_assoc, ← Finset.prod_mul_distrib]
    gcongr with v
    exact hCφ v h h' _
  ·
    have hpsi : ∀ c, S.psiInf 0 c = 1 := by
      intro c
      simp [C.HidaSetting.psiInf]
    simp only [C.HidaSetting.Nhat, hpsi, mul_one]
    have hae : S.N1 ε i w.1 Y κ =ᵐ[volume] fun c => Φ (Qm S c) := by
      have hnull : volume (Qm S ⁻¹' (⋃ v, {y : Fin S.f → ℂ | y v = 0})) = 0 := by
        rw [(Qm_mp S).measure_preimage (MeasurableSet.iUnion fun v =>
          measurableSet_eq_fun (measurable_pi_apply v) measurable_const).nullMeasurableSet]
        exact measure_iUnion_null fun v => Measure.pi_hyperplane _ v 0
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with c hc
      apply hN1 c
      intro v hv
      exact hc (Set.mem_preimage.mpr (Set.mem_iUnion.mpr ⟨v, by simp [Qm_apply, hv]⟩))
    have hmap : ∫ c, Φ (Qm S c) = ∫ y, Φ y := by
      conv_rhs => rw [← (Qm_mp S).map_eq]
      rw [integral_map (Qm_mp S).measurable.aemeasurable hΦc.aestronglyMeasurable]
    have hint : ∀ (h h' : Y), Integrable (fun y : Fin S.f → ℂ => ∏ v, φ v h h' (y v)) :=
      fun h h' => Integrable.fintype_prod (fun v => integrable_of_decay (hφc v h h') (hCφ v h h'))
    have hΦi : ∫ y, Φ y = (∑ h : Y, ∑ h' : Y, κ h h' *
        ((ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) : ℂ) *
          S.gram ε (i - 1) w.1 h h')) / sz := by
      simp only [hΦ]
      rw [integral_div, integral_finsetSum _ fun h _ =>
        integrable_finsetSum _ fun h' _ => (hint h h').const_mul _]
      congr 1
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [integral_finsetSum _ fun h' _ => (hint h h').const_mul _]
      refine Finset.sum_congr rfl fun h' _ => ?_
      rw [integral_const_mul, integral_fintype_prod_volume_eq_prod]
      congr 1
      simp only [hφi, Finset.prod_mul_distrib, C.HidaSetting.gram, if_pos (show i - 1 ≤ S.G.r + 1 by omega)]
      rw [← Complex.ofReal_prod, hprod i hi1 hi2]

    have hκH : ∀ h ∈ Y, ∀ h' ∈ Y, conj (κ h h') = κ h' h := by
      intro h hh h' hh'
      exact hκ.1.apply (⟨h', hh'⟩ : Y) (⟨h, hh⟩ : Y)
    have hgH : ∀ h h' : TB.Pt E, conj (S.gram ε (i - 1) w.1 h h') = S.gram ε (i - 1) w.1 h' h := by
      intro h h'
      simp only [C.HidaSetting.gram, if_pos (show i - 1 ≤ S.G.r + 1 by omega), map_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      have hP := hpos v ε hε (i - 1) (by omega) w {C.loc (S.σ v) h, C.loc (S.σ v) h'}
      exact hP.1.apply (⟨C.loc (S.σ v) h', by simp⟩ : ({C.loc (S.σ v) h, C.loc (S.σ v) h'} : Finset C.LPt))
        (⟨C.loc (S.σ v) h, by simp⟩ : ({C.loc (S.σ v) h, C.loc (S.σ v) h'} : Finset C.LPt))
    set X : ℂ := ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * S.gram ε (i - 1) w.1 h h' with hX
    have hXr : ((X.re : ℝ) : ℂ) = X := by
      rw [← Complex.conj_eq_iff_re, hX, map_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun h' hh' => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [map_mul, hκH h' hh' h hh, hgH h' h]
    have hN0 : ((S.base.N0 ε (i - 1) w Y κ : ℝ) : ℂ) = X / sz := by
      show (((X.re / C.Word.size S.P w.1 : ℝ)) : ℂ) = X / sz
      rw [Complex.ofReal_div, hXr]
    rw [hN0, integral_congr_ae hae, hmap, hΦi]
    have hcv := hcov i hi1 hi2
    set cv : ℝ := ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) with hcvd
    have hcv' : (cv : ℂ) ≠ 0 := by exact_mod_cast hcv
    have hsum : ∑ h : Y, ∑ h' : Y, κ h h' * ((cv : ℂ) * S.gram ε (i - 1) w.1 h h') = (cv : ℂ) * X := by
      rw [hX, Finset.mul_sum, ← Finset.sum_coe_sort Y]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_coe_sort Y]
      refine Finset.sum_congr rfl fun h' _ => ?_
      ring
    rw [hsum]
    field_simp
end Formalism.FourierDecayAlt.P.JCx1.needs
