-- Prove2me | solution 1 for Formalism.CountingSumsFrames.XD_keep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:44:25.651381+00:00
-- url     : https://prove2.me/submissions/241ac059-273f-4806-baa6-70ebbb1c214b

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {k σ : Type} [Field k]
namespace Formalism.CountingSumsFrames
theorem _root_.solution (u v : σ) (Q Q' : Set (σ →₀ ℕ))
    (h : ∀ m ∈ Q, 1 ≤ m v → Finsupp.single u 1 + (m - Finsupp.single v 1) ∈ Q') :
    ∀ x ∈ restrictSupport k Q, X u * pderiv v x ∈ restrictSupport k Q' := by
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx
  rw [MvPolynomial.as_sum x, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hmQ : m ∈ Q := hx hm
  rw [pderiv_monomial, X, monomial_mul, one_mul]
  by_cases hv : m v = 0
  · rw [hv, Nat.cast_zero, mul_zero, map_zero]
    exact Submodule.zero_mem _
  · rw [MvPolynomial.mem_restrictSupport_iff]
    refine (Finset.coe_subset.mpr support_monomial_subset).trans ?_
    rw [Finset.coe_singleton, Set.singleton_subset_iff]
    exact h m hmQ (Nat.one_le_iff_ne_zero.mpr hv)
end Formalism.CountingSumsFrames
