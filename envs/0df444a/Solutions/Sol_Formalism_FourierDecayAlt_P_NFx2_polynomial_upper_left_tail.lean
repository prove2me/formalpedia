-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.polynomial_upper_left_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:05:53.09632+00:00
-- url     : https://prove2.me/submissions/534ee2bd-3a11-4ad6-9ed6-26d0445f3084

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_polynomial_coordinate
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_polynomial_raising
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_polynomial_lowering
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_polynomial_lower_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_polynomial_upper_sum

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution : IsPF fun Y => upperLeftTail L κ SS Y := by
  unfold upperLeftTail
  exact isPF_add (isPF_add (isPF_mul (isPF_mul (isPF_mul (isPF_const _) polynomial_coordinate) polynomial_raising) polynomial_lowering)
    (isPF_mul (isPF_mul (isPF_mul (isPF_const _) polynomial_raising) (isPF_const _)) polynomial_lower_sum))
    (isPF_mul polynomial_upper_sum polynomial_lowering)
end Formalism.FourierDecayAlt.P.NFx2
