-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.gNpow_inCC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:06:08.915025+00:00
-- url     : https://prove2.me/submissions/7bcebca3-1c51-492d-bc4c-558491edab41

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiRegOf
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MapInvMEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_gN_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_ckOn_zero_of_contOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_rpow_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_NInt_gN_cont
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
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution (hNI : NormInv) (b : ℝ) (hb : b ≠ 0) :
    B.InCC b 0 (fun g : B.Mat k r => ((B.gN g ^ (-b) : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)) := by
  have hpos : ∀ g ∈ B.GV k r, 0 < B.gN g := fun g hg => lt_of_lt_of_le one_pos ((hNI k r).2 g hg).2
  have hf : ContinuousOn (fun g : Mx k r => ((B.gN g ^ (-b) : ℝ) : ℂ)) (B.GV k r) := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact gN_cont.continuousOn.rpow_const (fun g hg => Or.inl (hpos g hg).ne')
  refine ⟨1, ckOn_zero_of_contOn _ hf, ?_⟩
  intro uu vv _ _ hlen g hg
  have hu : uu = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hv : vv = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hu; subst hv
  show B.gN g ^ b * ‖((B.gN g ^ (-b) : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)‖ ≤ 1
  have hgN : 0 ≤ B.gN g := Real.sqrt_nonneg _
  rw [norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hgN _)]
  have := rpow_bound (B.gN g) 1 b hgN hb
  simpa using this
end Formalism.FourierDecayAlt.P.S3dx4
