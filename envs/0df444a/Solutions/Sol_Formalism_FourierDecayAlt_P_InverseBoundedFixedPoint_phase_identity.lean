-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.phase_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:41.158091+00:00
-- url     : https://prove2.me/submissions/0a0c9abb-369d-4ad4-ac88-68478d49bbf7

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_prod_ordered

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
theorem _root_.solution (y w : Fin m → K) (h : ∀ k, (1 + y k) * w k = 1) :
    ∑ k, y k + ∏ k, w k - 1 = ∑ i, y i ^ 2 * w i +
      ∑ i, ∑ j, if j < i then y i * uW w i j * y j else 0 := by
  have h1 : ∏ k, w k = 1 - ∑ i, (y i * w i) * piW w i := prod_ordered y w h Finset.univ
  have h2 : ∀ i, piW w i = 1 - ∑ j, if j < i then (y j * w j) * piW w j else 0 := by
    intro i
    rw [← Finset.sum_filter]
    unfold piW
    rw [prod_ordered y w h]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j < i := (Finset.mem_filter.1 hj).2
    rw [Finset.filter_filter]
    congr 2
    refine Finset.filter_congr fun k _ => ⟨fun hk => hk.2, fun hk => ⟨hk.trans hji, hk⟩⟩
  rw [h1, ← Finset.sum_add_distrib]
  have e : ∑ k, y k + (1 - ∑ i, (y i * w i) * piW w i) - 1 = ∑ i, (y i - (y i * w i) * piW w i) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [e]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [h2 i]
  have e2 : ∑ j, (if j < i then y i * uW w i j * y j else 0) =
      (y i * w i) * ∑ j, if j < i then (y j * w j) * piW w j else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold uW
    split_ifs <;> ring
  rw [e2]
  linear_combination (-(y i)) * h i
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
