-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.third_polynomial_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:21:30.365872+00:00
-- url     : https://prove2.me/submissions/6ab93f97-58dc-4272-8bc8-a105486637f7

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SignPermutationIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPolynomialExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_succAbove_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_zb_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution : MinorsThirdCase := by
  intro i0 s'' h t
  rw [← zb_det i0 s'' h t]
  congr 1
  ext a b
  simp only [Matrix.of_apply, succAbove_val]
  have ha := a.isLt
  have hb := b.isLt
  by_cases ha0 : (a : ℕ) < i0 <;> by_cases hb0 : (b : ℕ) < i0 <;>
    simp only [ha0, hb0, if_true, if_false] <;>
    unfold Zb <;> split_ifs <;> first | rfl | omega
end Formalism.FourierDecayAlt.P.SignAntidiagonal
