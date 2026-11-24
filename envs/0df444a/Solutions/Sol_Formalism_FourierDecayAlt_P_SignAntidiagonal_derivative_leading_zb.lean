-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:21:22.832876+00:00
-- url     : https://prove2.me/submissions/a82bd3bf-4e7a-419a-9adb-0f0d3ba01cc5

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SignPermutationIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPolynomialExpansion
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
theorem _root_.solution : DleadZb := by
  intro i0 s h t
  refine ⟨?_, zb_det i0 s h t⟩
  unfold Dlead
  congr 1
  ext a b
  simp [Zb, a.isLt, b.isLt]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
