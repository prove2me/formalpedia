-- Prove2me | solution 1 for DeletedPrimes.tsum_muS_div_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:00:43.651527+00:00
-- url     : https://prove2.me/submissions/0cb4bf76-78a8-4a52-8888-63c9f9fa0409

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution (hsum : Summable fun d : ℕ => (muS S d : ℝ) / d) (x : ℝ) :
    ∑' d : ℕ, (muS S d : ℝ) / d = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ) / d
      + ∑' d : ℕ, (if x < d then (muS S d : ℝ) / d else 0) := by
  have hfin : ∀ d ∉ Finset.Icc 1 ⌊x⌋₊, (if x < d then 0 else (muS S d : ℝ) / d) = 0 := by
    intro d hd
    split_ifs with h
    · rfl
    · rcases Nat.eq_zero_or_pos d with rfl | hpos
      · simp
      · exfalso; apply hd
        refine Finset.mem_Icc.mpr ⟨hpos, ?_⟩
        push Not at h
        exact Nat.le_floor h
  have hB : Summable fun d : ℕ => (if x < d then 0 else (muS S d : ℝ) / d) :=
    (hasSum_sum_of_ne_finset_zero hfin).summable
  have hA : Summable fun d : ℕ => (if x < d then (muS S d : ℝ) / d else 0) := by
    refine Summable.of_norm_bounded hsum.abs fun d => ?_
    split_ifs
    · exact le_rfl
    · simp
  have hBsum : ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (if x < d then 0 else (muS S d : ℝ) / d) =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ) / d := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdx : (d : ℝ) ≤ x := by
      have h1 : d ≤ ⌊x⌋₊ := (Finset.mem_Icc.mp hd).2
      have hx0 : 0 ≤ x := by
        by_contra hneg
        push Not at hneg
        have : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
        have := (Finset.mem_Icc.mp hd).1
        omega
      exact le_trans (by exact_mod_cast h1) (Nat.floor_le hx0)
    rw [if_neg (not_lt.mpr hdx)]
  calc ∑' d : ℕ, (muS S d : ℝ) / d
      = ∑' d : ℕ, ((if x < d then (muS S d : ℝ) / d else 0)
          + (if x < d then 0 else (muS S d : ℝ) / d)) :=
        tsum_congr fun d => by split_ifs <;> simp
    _ = _ := by rw [Summable.tsum_add hA hB, tsum_eq_sum hfin, hBsum, add_comm]
end DeletedPrimes
