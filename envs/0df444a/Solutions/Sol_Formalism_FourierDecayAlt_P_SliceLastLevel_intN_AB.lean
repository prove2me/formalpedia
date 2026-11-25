-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.intN_AB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:18:23.98581+00:00
-- url     : https://prove2.me/submissions/93623e7d-6e73-4015-979c-b6d9e8578e4c

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SliceLastLevel
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_tr_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_gN_mul_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_gN_inv_GV
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_tr_f_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_tr_meas_bigCell
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_tr_cWeight_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_tr_f_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_tr_bigCell_one_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_mul_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_sf
import Theorems.Thm_Formalism_FourierDecayAlt_P_iterated_integration_formula
import Theorems.Thm_Formalism_FourierDecayAlt_P_norm_power_integrable_sharp
import Theorems.Thm_Formalism_FourierDecayAlt_P_opposite_weyl_haar_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_unitary_group_haar_exists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology
set_option linter.style.haveILetI false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution {μN : Measure (Mt k r)} (hN : IsHaarOn (Nset k r) μN) :
    ∫⁻ x, ENNReal.ofReal (B.gN (Matrix.of x : B.Mat k r) ^ (-(B.AB k r))) ∂μN < ⊤ := by
  classical
  haveI := P.LongWeylElement.sf hN
  obtain ⟨μG, hG⟩ := P.unitary_group_haar_exists k r
  obtain ⟨μb, hb⟩ := P.opposite_weyl_haar_exists k r
  haveI := P.LongWeylElement.sf hb
  set A := B.AB k r with hA
  have hA0 : 0 ≤ A := by
    rw [hA]; unfold B.AB; positivity
  set f : Mt k r → ENNReal := fun g => ENNReal.ofReal (B.gN (Matrix.of g : B.Mat k r) ^ (-A)) with hfdef
  have hfm : Measurable f := tr_f_meas A
  obtain ⟨C, hC, hI⟩ := P.iterated_integration_formula k r μG μN μb hG hN hb
  have hfin : (∫⁻ g, f g ∂μG) < ⊤ := P.norm_power_integrable_sharp k r μG A hG le_rfl
  rw [hI f hfm] at hfin
  set IN := ∫⁻ x, f x ∂μN with hIN
  set Ib := ∫⁻ x, f x ∂μb with hIbdef

  have hIb : Ib ≠ 0 := by
    intro h0
    have h1 := (lintegral_eq_zero_iff hfm).1 h0
    have h2 : ∀ᵐ x ∂μb, False := by
      filter_upwards [h1, P.LongWeylElement.haar_ae hb] with x hx hxU
      have := tr_f_pos (A := A) hxU.1
      simp only [Pi.zero_apply] at hx
      exact absurd hx (ne_of_gt this)
    have h3 : μb Set.univ = 0 := by
      have := ae_iff.1 h2
      simpa using this
    exact hb.ne_zero (Measure.measure_univ_eq_zero.1 h3)

  set S : Set (Fin r → ℂ) := {c | ∀ a, c a ≠ 0} with hSdef
  have hSo : IsOpen S := by
    have : S = ⋂ a : Fin r, (fun c : Fin r → ℂ => c a) ⁻¹' {0}ᶜ := by
      ext c; simp [hSdef]
    rw [this]
    exact isOpen_iInter_of_finite fun a => isOpen_compl_singleton.preimage (continuous_apply a)
  have hSm : MeasurableSet S := hSo.measurableSet

  have hinner : ∀ c ∈ S, ENNReal.ofReal (B.gN (bigCell k r c 1) ^ (-A)) * (IN * IN * Ib) ≤
      ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
        f ((Matrix.of p.1.1)⁻¹ * bigCell k r c 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂((μN.prod μN).prod μb) := by
    intro c hc
    have hbG := tr_bigCell_one_mem (k := k) hc
    have hae1 : ∀ᵐ p ∂((μN.prod μN).prod μb), (Matrix.of p.1.1 : B.Mat k r) ∈ Nset k r :=
      Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae (P.LongWeylElement.haar_ae hN))
    have hae2 : ∀ᵐ p ∂((μN.prod μN).prod μb), (Matrix.of p.1.2 : B.Mat k r) ∈ Nset k r :=
      Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae (P.LongWeylElement.haar_ae hN))
    have hae3 : ∀ᵐ p ∂((μN.prod μN).prod μb), (Matrix.of p.2 : B.Mat k r) ∈ B2.UWb k r :=
      Measure.quasiMeasurePreserving_snd.ae (P.LongWeylElement.haar_ae hb)
    set β : ENNReal := ENNReal.ofReal (B.gN (bigCell k r c 1) ^ (-A)) with hβ
    have hpt : ∀ᵐ p ∂((μN.prod μN).prod μb),
        β * ((f p.1.1 * f p.1.2) * f p.2) ≤
          f ((Matrix.of p.1.1)⁻¹ * bigCell k r c 1 * Matrix.of p.2 * Matrix.of p.1.2) := by
      filter_upwards [hae1, hae2, hae3] with p h1 h2 h3
      set n : B.Mat k r := Matrix.of p.1.1
      set n' : B.Mat k r := Matrix.of p.1.2
      set m : B.Mat k r := Matrix.of p.2
      have hn : n ∈ B.GV k r := h1.1
      have hn' : n' ∈ B.GV k r := h2.1
      have hm : m ∈ B.GV k r := h3.1
      have hgG : n⁻¹ * bigCell k r c 1 * m * n' ∈ B.GV k r :=
        P.BetaSesquilinearity.gv_mul (P.BetaSesquilinearity.gv_mul (P.BetaSesquilinearity.gv_mul (P.BetaSesquilinearity.gv_inv hn) hbG) hm) hn'
      have hgpos : 0 < B.gN (n⁻¹ * bigCell k r c 1 * m * n') :=
        lt_of_lt_of_le one_pos (P.BetaSesquilinearity.gN_ge_one hgG)
      have hle : B.gN (n⁻¹ * bigCell k r c 1 * m * n') ≤
          B.gN n * B.gN (bigCell k r c 1) * B.gN m * B.gN n' := by
        calc B.gN (n⁻¹ * bigCell k r c 1 * m * n') ≤ B.gN (n⁻¹ * bigCell k r c 1 * m) * B.gN n' := gN_mul_le _ _
          _ ≤ (B.gN (n⁻¹ * bigCell k r c 1) * B.gN m) * B.gN n' :=
              mul_le_mul_of_nonneg_right (gN_mul_le _ _) (tr_gN_nonneg _)
          _ ≤ ((B.gN n⁻¹ * B.gN (bigCell k r c 1)) * B.gN m) * B.gN n' :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (gN_mul_le _ _) (tr_gN_nonneg _))
                (tr_gN_nonneg _)
          _ = B.gN n * B.gN (bigCell k r c 1) * B.gN m * B.gN n' := by rw [gN_inv_GV hn]
      have hrp := Real.rpow_le_rpow_of_nonpos hgpos hle (by linarith : -A ≤ 0)
      have e1 : (B.gN n * B.gN (bigCell k r c 1) * B.gN m * B.gN n') ^ (-A) =
          B.gN n ^ (-A) * B.gN (bigCell k r c 1) ^ (-A) * B.gN m ^ (-A) * B.gN n' ^ (-A) := by
        rw [Real.mul_rpow (mul_nonneg (mul_nonneg (tr_gN_nonneg _) (tr_gN_nonneg _)) (tr_gN_nonneg _))
            (tr_gN_nonneg _),
          Real.mul_rpow (mul_nonneg (tr_gN_nonneg _) (tr_gN_nonneg _)) (tr_gN_nonneg _),
          Real.mul_rpow (tr_gN_nonneg _) (tr_gN_nonneg _)]
      rw [e1] at hrp
      have hnn : ∀ g : B.Mat k r, 0 ≤ B.gN g ^ (-A) := fun g => Real.rpow_nonneg (tr_gN_nonneg _) _
      calc β * ((f p.1.1 * f p.1.2) * f p.2)
          = ENNReal.ofReal (B.gN n ^ (-A) * B.gN (bigCell k r c 1) ^ (-A) * B.gN m ^ (-A) * B.gN n' ^ (-A)) := by
            rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (hnn _) (hnn _)) (hnn _)),
              ENNReal.ofReal_mul (mul_nonneg (hnn _) (hnn _)), ENNReal.ofReal_mul (hnn _)]
            simp only [hfdef, hβ]
            ring
        _ ≤ f ((Matrix.of p.1.1)⁻¹ * bigCell k r c 1 * Matrix.of p.2 * Matrix.of p.1.2) :=
            ENNReal.ofReal_le_ofReal hrp
    refine le_trans (le_of_eq ?_) (lintegral_mono_ae hpt)
    have hm3 : Measurable (fun p : (Mt k r × Mt k r) × Mt k r => f p.1.1 * f p.1.2 * f p.2) :=
      ((hfm.comp (measurable_fst.comp measurable_fst)).mul (hfm.comp (measurable_snd.comp measurable_fst))).mul
        (hfm.comp measurable_snd)
    have hm2 : Measurable (fun q : Mt k r × Mt k r => f q.1 * f q.2) :=
      (hfm.comp measurable_fst).mul (hfm.comp measurable_snd)
    have e1 : ∫⁻ p : (Mt k r × Mt k r) × Mt k r, f p.1.1 * f p.1.2 * f p.2 ∂((μN.prod μN).prod μb) =
        (∫⁻ q : Mt k r × Mt k r, f q.1 * f q.2 ∂(μN.prod μN)) * Ib :=
      lintegral_prod_mul (f := fun q : Mt k r × Mt k r => f q.1 * f q.2) (g := f) hm2.aemeasurable hfm.aemeasurable
    have e2 : ∫⁻ q : Mt k r × Mt k r, f q.1 * f q.2 ∂(μN.prod μN) = IN * IN :=
      lintegral_prod_mul (f := f) (g := f) hfm.aemeasurable hfm.aemeasurable
    rw [lintegral_const_mul _ hm3, e1, e2]

  set F : (Fin r → ℂ) → ENNReal := fun c => ENNReal.ofReal (B2.cWeight k r c) *
    ENNReal.ofReal (B.gN (bigCell k r c 1) ^ (-A)) with hFdef
  have hFm : Measurable F :=
    (ENNReal.measurable_ofReal.comp tr_cWeight_cont.measurable).mul (hfm.comp tr_meas_bigCell)
  set K := ∫⁻ c, S.indicator F c with hKdef
  have hK : K ≠ 0 := by
    intro h0
    have h1 := (lintegral_eq_zero_iff (hFm.indicator hSm)).1 h0
    have hpos : ∀ c ∈ S, S.indicator F c ≠ 0 := by
      intro c hc
      rw [Set.indicator_of_mem hc]
      refine ne_of_gt (ENNReal.mul_pos ?_ ?_)
      · refine ne_of_gt (ENNReal.ofReal_pos.2 ?_)
        unfold B2.cWeight
        exact Finset.prod_pos fun a _ => pow_pos (norm_pos_iff.2 (hc a)) _
      · exact ne_of_gt (tr_f_pos (tr_bigCell_one_mem hc))
    have h2 : (volume : Measure (Fin r → ℂ)) S = 0 := by
      refine measure_mono_null (fun c hc => ?_) (ae_iff.1 h1)
      exact hpos c hc
    have h3 := hSo.measure_pos (volume : Measure (Fin r → ℂ)) ⟨fun _ => 1, fun a => one_ne_zero⟩
    exact absurd h2 (ne_of_gt h3)
  have hlow : K * (IN * IN * Ib) ≤ ∫⁻ c, ENNReal.ofReal (B2.cWeight k r c) *
      ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
        f ((Matrix.of p.1.1)⁻¹ * bigCell k r c 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂((μN.prod μN).prod μb) := by
    rw [hKdef, ← lintegral_mul_const _ (hFm.indicator hSm)]
    refine lintegral_mono fun c => ?_
    by_cases hc : c ∈ S
    · rw [Set.indicator_of_mem hc, hFdef, mul_assoc]
      gcongr
      exact hinner c hc
    · rw [Set.indicator_of_notMem hc, zero_mul]
      exact zero_le
  have hfin2 : (C : ENNReal) * (K * (IN * IN * Ib)) < ⊤ := by
    refine lt_of_le_of_lt ?_ hfin
    gcongr
  by_contra htop
  have hIN : IN = ⊤ := not_lt_top_iff.1 htop
  have hCne : (C : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hC)
  rw [hIN, ENNReal.top_mul (by simp), ENNReal.top_mul hIb, ENNReal.mul_top hK, ENNReal.mul_top hCne] at hfin2
  exact lt_irrefl _ hfin2
end Formalism.FourierDecayAlt.P.SliceLastLevel
