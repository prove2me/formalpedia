-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.shift_shift_relation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:36.21721+00:00
-- url     : https://prove2.me/submissions/eab510c5-2354-4f53-8373-757e3c42ffbb

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_kap_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Mx4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.SSShift := by
  intro P l f g h
  rw [kap_eq, kap_eq]
  ext π' π
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hu : Up P l π π'
  · simp only [SS, Matrix.of_apply, if_pos hu, h π π' hu]
    exact (Algebra.commutes _ _)
  · simp [SS, hu]
end Formalism.FourierDecayAlt.P
