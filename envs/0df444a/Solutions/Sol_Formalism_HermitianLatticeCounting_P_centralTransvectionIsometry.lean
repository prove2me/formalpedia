-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.centralTransvectionIsometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:07:05.926855+00:00
-- url     : https://prove2.me/submissions/9b7019be-ba47-4c48-a877-09e29c99d5ea

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : CentreIsometry := by
  intro R V _ _ _ _ h hh r e c he hc x y
  have hc' : ∀ a a', star (c a a') = - c a' a := by
    intro a a'
    have := congrFun (congrFun hc a') a
    simpa [Matrix.conjTranspose_apply] using this
  have hL : ∀ (k : Fin r → Fin r → R) (z : V),
      h (∑ a, ∑ a', k a a' • e a) z = ∑ a, ∑ a', k a a' * h (e a) z := by
    intro k z; simp [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  have hR : ∀ (k : Fin r → Fin r → R) (z : V),
      h z (∑ a, ∑ a', k a a' • e a) = ∑ a, ∑ a', star (k a a') * h z (e a) := by
    intro k z; simp [map_sum, map_smulₛₗ, starRingEnd_apply]
  have hy : ∀ a, h (e a) y = star (h y (e a)) := fun a => hh y (e a)
  simp only [map_add, LinearMap.add_apply, hL, hR, he, hy, mul_zero, Finset.sum_const_zero,
    add_zero]
  have key : ∑ a, ∑ a', star (c a a' * h y (e a')) * h x (e a) =
      - ∑ a, ∑ a', c a a' * h x (e a') * star (h y (e a)) := by
    simp only [star_mul', hc']
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro a' _; ring
  linear_combination key
end Formalism.HermitianLatticeCounting.P
