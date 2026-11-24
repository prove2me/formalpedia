-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_eq_support_of_isDerivBalanced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:26:20.643508+00:00
-- url     : https://prove2.me/submissions/aa3ea861-107c-4549-8235-5ad2c6badd2d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtMultiplicativity
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivBalancedOrderLocus
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_orderAtLeastLocus_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_one_le_orderAt_iff_mem_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_zero_iff_not_mem_support


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
  (I : X.IdealSheafData) (m : ℕ)
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution
    (h : IsDerivBalanced k p I m) (hm : 1 ≤ m) :
    orderAtLeastLocus I m = (I.support : Set X) := by
  ext x
  rw [mem_orderAtLeastLocus_iff]
  constructor
  · intro hx
    have h1 : (1 : ℕ∞) ≤ orderAt I x := le_trans (by exact_mod_cast hm) hx
    exact (one_le_orderAt_iff_mem_support I x).mp h1
  · intro hx
    have hx' : x ∈ I.support := hx
    have hne : orderAt I x ≠ 0 := fun h0 =>
      (orderAt_eq_zero_iff_not_mem_support I x).mp h0 hx'
    rcases orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced k p I m h x with h0 | h0
    · exact absurd h0 hne
    · exact h0
end FunctorialResolution.EmbeddedResolution
