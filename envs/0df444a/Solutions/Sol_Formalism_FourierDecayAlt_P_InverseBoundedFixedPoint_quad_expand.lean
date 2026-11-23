-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.quad_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:54.336523+00:00
-- url     : https://prove2.me/submissions/d473d373-5dfb-4ef0-90d0-6d3236e090b2

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
theorem _root_.solution (y w : Fin m → K) :
    y ⬝ᵥ (MW w *ᵥ y) = 2 * (∑ i, y i ^ 2 * w i +
      ∑ i, ∑ j, if j < i then y i * uW w i j * y j else 0) := by
  have e : ∀ i j, y i * (MW w i j * y j) = (if i = j then 2 * (y i ^ 2 * w i) else 0) +
      (if j < i then y i * uW w i j * y j else 0) + (if i < j then y j * uW w j i * y i else 0) := by
    intro i j
    simp only [MW, Matrix.of_apply]
    by_cases hij : i = j
    · subst hij; simp; ring
    · simp only [hij, if_false]
      split_ifs <;> ring
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, e, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if i < j then y j * uW w j i * y i else 0)]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.mul_sum]
  ring
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
