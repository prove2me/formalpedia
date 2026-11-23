-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.orthogonalMeanNorm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:47.903428+00:00
-- url     : https://prove2.me/submissions/3de5b62e-dc8d-4321-9adb-e472a80b1685

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialMeansOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x1_norm_sq_sum_orth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.OrthNorm := by
  intro E _ _ A _ P e₁ he h
  rw [norm_smul, mul_pow, A6x1.norm_sq_sum_orth P e₁ he h, norm_inv, Complex.norm_natCast]
end Formalism.FourierDecayAlt.P
