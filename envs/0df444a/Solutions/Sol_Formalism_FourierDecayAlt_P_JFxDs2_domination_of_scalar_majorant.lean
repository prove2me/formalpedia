-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxDs2.domination_of_scalar_majorant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:57:14.624881+00:00
-- url     : https://prove2.me/submissions/843a0d5c-5dbb-4eef-9938-a054c606e6a7

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalMeasurabilityWeakThreshold
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_bound_scaled
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cc_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_length_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_lrt_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_norm_rho_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_sgs_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs2_allLie_ad
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs2_pn_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs2_sL_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs2_sR_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_cc_nonneg
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
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxDs2
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.JFxDs2
theorem _root_.solution : Formalism.FourierDecayAlt.P.WeakThresholdClauses.NNMajW → Formalism.FourierDecayAlt.P.WeakThresholdClauses.JDomBoundW := by
  intro hN k r Wp Wq _ _ _ _ _ _ D A m F hThr hF K hK hKO
  obtain ⟨c, hc⟩ := hF
  have hc0 : 0 ≤ c := B4.cc_nonneg hc
  obtain ⟨b, hb, hbd⟩ := hN k r Wp Wq D A m hThr K hK hKO
  refine ⟨fun p => c * b p, hb.const_mul c, fun u v hu hv hl g hg => ?_⟩
  filter_upwards [hbd u v hu hv hl g hg, B5.ae_inSS D] with p hp hSS
  have hgG : g ∈ GV k r := (hKO hg).1
  have hx : sgs p g ∈ GV k r := B7.sgs_mem D hSS hgG
  have hpos : 0 < gN (sgs p g) := B6.gN_pos hx
  have hw := allLie_ad (sL_mem hSS) (sR_mem hSS) hu hv
  have hB := B4.bound_scaled hc (B4.lr (u.map (AdL p)) (v.map (AdR p))) (B4.lrt_lr _ _) hw
    (by rw [B4.length_lr]; simpa using hl) _ hx
  rw [← B4.dLR_eq, pn_lr] at hB
  have hApos : 0 < gN (sgs p g) ^ A := Real.rpow_pos_of_pos hpos A
  have h1 : ‖dLR (u.map (AdL p)) (v.map (AdR p)) F (sgs p g)‖ ≤
      c * ((u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod * gN (sgs p g) ^ (-A)) := by
    rw [Real.rpow_neg hpos.le]
    rw [mul_comm (gN (sgs p g) ^ A) _, ← le_div_iff₀ hApos] at hB
    calc _ ≤ _ := hB
      _ = _ := by rw [div_eq_mul_inv]; ring
  calc ‖rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖
      ≤ ‖dLR (u.map (AdL p)) (v.map (AdR p)) F (sgs p g)‖ := B7.norm_rho_le D hSS _ g
    _ ≤ _ := h1
    _ ≤ c * b p := mul_le_mul_of_nonneg_left hp hc0
end Formalism.FourierDecayAlt.P.JFxDs2
