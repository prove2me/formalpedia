-- Prove2me | solution 1 for DeletedPrimes.summable_units_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:02:03.501835+00:00
-- url     : https://prove2.me/submissions/53fd8047-ba97-4bbb-8a91-087dceb30254

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
import Theorems.Thm_DeletedPrimes_sum_range_units_le

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution {σ : ℝ}
    (h : Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-σ))) :
    Summable fun d : ℕ => |(muS S d : ℝ)| * (d : ℝ) ^ (-σ) := by
  have hnn : ∀ n : ℕ, 0 ≤ S.indicator (fun n : ℕ => (n : ℝ) ^ (-σ)) n := fun n =>
    Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) n
  refine summable_of_sum_range_le
    (c := Real.exp (∑' n, S.indicator (fun n : ℕ => (n : ℝ) ^ (-σ)) n))
    (fun d => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)) fun N => ?_
  refine le_trans (sum_range_units_le σ N) ?_
  have hP : ∑ p ∈ (Finset.range N).filter (· ∈ S), (p : ℝ) ^ (-σ) =
      ∑ n ∈ Finset.range N, S.indicator (fun n : ℕ => (n : ℝ) ^ (-σ)) n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Set.indicator_apply]
  calc ∏ p ∈ (Finset.range N).filter (· ∈ S), (1 + (p : ℝ) ^ (-σ))
      ≤ ∏ p ∈ (Finset.range N).filter (· ∈ S), Real.exp ((p : ℝ) ^ (-σ)) := by
        refine Finset.prod_le_prod (fun p _ => ?_) (fun p _ => ?_)
        · have := Real.rpow_nonneg (Nat.cast_nonneg p) (-σ); linarith
        · rw [add_comm]; exact Real.add_one_le_exp _
    _ = Real.exp (∑ p ∈ (Finset.range N).filter (· ∈ S), (p : ℝ) ^ (-σ)) :=
        (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' n, S.indicator (fun n : ℕ => (n : ℝ) ^ (-σ)) n) := by
        rw [Real.exp_le_exp, hP]
        exact h.sum_le_tsum _ fun n _ => hnn n
end DeletedPrimes
