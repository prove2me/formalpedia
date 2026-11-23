-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.HA_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:33.046714+00:00
-- url     : https://prove2.me/submissions/5b1915dd-d5d3-4a1a-a47b-7b5b36ecabe6

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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
theorem _root_.solution (R : Subring K) (m : ℕ) (i j : Fin m) : HA K m i j ∈ R := by
  simp only [HA, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
  refine R.sub_mem (R.mul_mem (natCast_mem R _) ?_) R.one_mem
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
