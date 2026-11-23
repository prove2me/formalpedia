-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.hess_one_bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:11.158035+00:00
-- url     : https://prove2.me/submissions/28dd5b83-c042-42f9-9010-4f050c1e77c4

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mul_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mul_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hess_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hs_lift_hess
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hs_lift_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hs_lift_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hs_inv_pow
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {A : Type} [CommRing A]
variable {K : Type} [CommRing K] {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (hϖ : (ϖ : K) ∈ R) {n a : ℕ} {t : K} (M : Matrix (Fin n) (Fin n) K) (h : IsHess t M)
    (ht : Bd R ϖ a t) (hM : ∀ i j, Bd R ϖ a (M i j)) :
    ∃ r, Bd R ϖ (n * a) r ∧ M.det = ∏ i, M i i + t * r := by
  obtain ⟨r, hr⟩ := hess_one (hs_lift M hM) (hs_lift_hess M h ht hM)
  have hr' : ((ϖ : K) ^ a) ^ n * M.det =
      ((ϖ : K) ^ a) ^ n * ∏ i, M i i + (ϖ : K) ^ a * t * (r : K) := by
    have := congrArg (fun x : R => (x : K)) hr
    simp only [Subring.coe_add, Subring.coe_mul] at this
    rw [hs_lift_det, hs_lift_prod] at this
    exact this
  have hi := hs_inv_pow (ϖ := ϖ) a n
  refine ⟨(((ϖ⁻¹ : Kˣ) : K) ^ a) ^ n * ((ϖ : K) ^ a * (r : K)), ?_, ?_⟩
  · have : (ϖ : K) ^ (n * a) * ((((ϖ⁻¹ : Kˣ) : K) ^ a) ^ n * ((ϖ : K) ^ a * (r : K))) =
        (ϖ : K) ^ a * (r : K) := by
      rw [mul_comm n a, pow_mul]
      linear_combination ((ϖ : K) ^ a * (r : K)) * hi
    unfold Bd
    rw [this]
    exact R.mul_mem (R.pow_mem hϖ a) r.2
  · linear_combination ((((ϖ⁻¹ : Kˣ) : K) ^ a) ^ n) * hr' + (∏ i, M i i - M.det) * hi
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
