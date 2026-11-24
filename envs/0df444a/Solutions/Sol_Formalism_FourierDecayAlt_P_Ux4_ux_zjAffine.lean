-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.ux_zjAffine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:38:06.423628+00:00
-- url     : https://prove2.me/submissions/4ceabd81-8a64-49a6-a01c-0d1d03af0ab2

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_symmetricScalarBlockMatrix_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
namespace Formalism.FourierDecayAlt.P.Ux4
theorem _root_.solution : ZjAffine := by
  intro p s a b H CC
  unfold Zj
  rw [symmetricScalarBlockMatrix_mul, symmetricScalarBlockMatrix_mul]
  simp
end Formalism.FourierDecayAlt.P.Ux4
