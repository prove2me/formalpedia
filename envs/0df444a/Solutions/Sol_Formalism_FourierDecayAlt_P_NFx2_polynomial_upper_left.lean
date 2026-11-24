-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.polynomial_upper_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:27:18.016801+00:00
-- url     : https://prove2.me/submissions/8b241c9d-abbe-4a51-b3b8-c7ba05c7afa7

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_polynomial_quartic_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_isPF_w
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_polynomial_upper_left_tail
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_upper_left_decomposition

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
theorem _root_.solution : IsPF fun Y => (Q.NFData.QQ (⟨L, κ, SS⟩ : Q.NFData P A) Y) 0 0 := by
  simp_rw [upper_left_decomposition]
  exact isPF_add (isPF_add (isPF_mul (isPF_const _) sn_isPF_w) polynomial_upper_left_tail) (isPF_mul (isPF_const _) polynomial_quartic_sum)
end Formalism.FourierDecayAlt.P.NFx2
