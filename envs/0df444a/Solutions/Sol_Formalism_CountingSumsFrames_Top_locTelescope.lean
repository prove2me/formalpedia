-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.locTelescope
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:38.700808+00:00
-- url     : https://prove2.me/submissions/df815c06-2984-4f80-ab58-01245afa5273

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ExistsNonzeroExchangedMinorHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
import Definitions.Def_Formalism_PolynomialDimension_DetMulEqSumAdjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Top
namespace Formalism.CountingSumsFrames.Top
theorem _root_.solution : Formalism.CountingSumsFrames.LocTelescope := by
  intro p J n' z hz hJ
  have key : ∀ m, m ≤ J → (∑ j ∈ Finset.range m, (z (j + 1) - z j)) + z 0 = z m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [Finset.sum_range_succ]
      have h1 := ih (by omega)
      have h2 := hz m (by omega)
      omega
  have hterm : ∀ j ∈ Finset.range J, (p : ℤ) ^ z j * ((p : ℤ) ^ (z (j + 1) - z j) - 1) =
      (p : ℤ) ^ z (j + 1) - (p : ℤ) ^ z j := by
    intro j hj
    have h := hz j (Finset.mem_range.mp hj)
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h]
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun j => (p : ℤ) ^ z j), hJ, pow_add]
    ring
  · rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    have := key J le_rfl
    omega
end Formalism.CountingSumsFrames.Top
