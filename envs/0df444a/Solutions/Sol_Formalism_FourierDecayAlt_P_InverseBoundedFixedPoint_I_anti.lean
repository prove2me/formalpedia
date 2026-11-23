-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.I_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:49:18.085821+00:00
-- url     : https://prove2.me/submissions/06c354a6-4bf3-4f3f-a22f-0d957c935cc4

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
theorem _root_.solution (hϖ : (ϖ : K) ∈ R) {n m : ℕ} (hnm : n ≤ m) {x : K} (hx : x ∈ I R ((ϖ : K) ^ m)) :
    x ∈ I R ((ϖ : K) ^ n) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact ⟨(ϖ : K) ^ d * r, R.mul_mem (R.pow_mem hϖ d) hr, by ring⟩
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
