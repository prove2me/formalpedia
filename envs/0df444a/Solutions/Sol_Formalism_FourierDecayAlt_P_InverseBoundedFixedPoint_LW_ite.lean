-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.LW.ite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:33.690118+00:00
-- url     : https://prove2.me/submissions/e7d6f3b1-bac5-4a94-b7fa-f469e8323c43

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_LW_const

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
variable {R : Subring K} {ϖ : Kˣ} {m : ℕ} {c : K}
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
namespace LW
theorem _root_.solution (p : Prop) [Decidable p] {f : (Fin m → K) → K} (hf : LW R c f) :
    LW R c (fun v => if p then f v else 0) := by
  by_cases hp : p
  · simpa [hp] using hf
  · simpa [hp] using LW.const (R := R) (c := c) (m := m) R.zero_mem
end LW
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
