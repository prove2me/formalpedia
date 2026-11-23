-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.MW_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:53.130886+00:00
-- url     : https://prove2.me/submissions/55b812fe-7888-46e4-b6de-fd501057a21c

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] {m : ℕ}
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
theorem _root_.solution : MW (fun _ : Fin m => (1 : K)) = HH K m := by
  ext i j
  simp only [MW, HH, uW, piW, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply,
    Finset.prod_const_one, mul_one]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.ne, h.le.not_gt]
  · subst h; simp; norm_num
  · simp [h, h.ne', h.le.not_gt]
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
