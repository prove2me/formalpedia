-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sb_raises
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:45:09.541595+00:00
-- url     : https://prove2.me/submissions/e674a532-e48b-4663-aef1-68e4841544d6

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_kap_mul_pj
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_pj_mul_kap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L0 : PreLevel A P.r}
  {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution : Raises κ (sb_SS κ QQ) := by
  intro l f g hfg
  unfold sb_SS
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  split_ifs with hc
  · have e1 : κ g * lowerBlockAlt κ QQ σ ρ regular_base_point = g σ • lowerBlockAlt κ QQ σ ρ regular_base_point := by
      rw [lowerBlockAlt, ← mul_assoc, ← mul_assoc, kap_mul_pj, smul_mul_assoc, smul_mul_assoc]
    have e2 : lowerBlockAlt κ QQ σ ρ regular_base_point * κ f = f ρ • lowerBlockAlt κ QQ σ ρ regular_base_point := by
      rw [lowerBlockAlt, mul_assoc, pj_mul_kap, mul_smul_comm]
    rw [sb_K, mul_smul_comm, smul_mul_assoc, e1, e2, hfg ρ σ hc.2]
  · rw [mul_zero, zero_mul]
end Formalism.FourierDecayAlt.P.NFx2
