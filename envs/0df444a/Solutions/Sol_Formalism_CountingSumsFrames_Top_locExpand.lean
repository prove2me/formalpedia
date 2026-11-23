-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.locExpand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:38.07728+00:00
-- url     : https://prove2.me/submissions/d94255b5-080f-4418-8710-97e58c2ed355

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
theorem _root_.solution : Formalism.CountingSumsFrames.LocExpand := by
  intro R _ ι _ _ J Del piI Q hJ
  classical
  have h0J : 0 ∈ Finset.range J := Finset.mem_range.mpr (by omega)
  have hexp : ∀ S : Finset ι, ∏ j ∈ Finset.range J, Del j ^ ((if j = 0 then 1 else 0) +
      Fintype.card ι * (Q j - 1) - S.card * (Q j - 1)) =
      Del 0 * (∏ j ∈ Finset.range J, Del j ^ (Q j - 1)) ^ (Fintype.card ι - S.card) := by
    intro S
    have hS : S.card ≤ Fintype.card ι := Finset.card_le_univ S
    have he : ∀ j, (if j = 0 then 1 else 0) + Fintype.card ι * (Q j - 1) - S.card * (Q j - 1) =
        (if j = 0 then 1 else 0) + (Q j - 1) * (Fintype.card ι - S.card) := by
      intro j
      have h1 : S.card * (Q j - 1) ≤ Fintype.card ι * (Q j - 1) := Nat.mul_le_mul_right _ hS
      rw [Nat.add_sub_assoc h1, ← Nat.sub_mul, mul_comm]
    simp only [he, pow_add, pow_mul, Finset.prod_mul_distrib, Finset.prod_pow]
    congr 1
    rw [Finset.prod_eq_single_of_mem 0 h0J (fun j _ hj => by simp [hj])]
    simp
  have hprod : ∏ I, (∏ j ∈ Finset.range J, Del j ^ (Q j - 1) -
      ∏ j ∈ Finset.range J, piI I j ^ (Q j - 1)) =
      ∑ S ∈ (Finset.univ : Finset ι).powerset, (∏ I ∈ S, -(∏ j ∈ Finset.range J, piI I j ^ (Q j - 1))) *
        ∏ I ∈ Finset.univ \ S, ∏ j ∈ Finset.range J, Del j ^ (Q j - 1) := by
    rw [← Finset.prod_add]
    exact Finset.prod_congr rfl fun I _ => by ring
  rw [hprod, Finset.mul_sum, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hneg : ∏ I ∈ S, -(∏ j ∈ Finset.range J, piI I j ^ (Q j - 1)) =
      (-1) ^ S.card * ∏ I ∈ S, ∏ j ∈ Finset.range J, piI I j ^ (Q j - 1) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun _ _ => by ring
  rw [hexp S, hneg, Finset.prod_const, ← Finset.compl_eq_univ_sdiff, Finset.card_compl]
  ring
end Formalism.CountingSumsFrames.Top
