-- Prove2me | solution 1 for DeletedPrimes.frequently_dense_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:08:01.714719+00:00
-- url     : https://prove2.me/submissions/7237360f-40fb-4852-af74-dea98d0a2945

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales
import Theorems.Thm_DeletedPrimes_two_pow_rpow

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} {σ η : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : σ < dim S) (hη : 0 < η) :
    ∃ᶠ j : ℕ in atTop, ((2 : ℝ) ^ j) ^ (σ - η) ≤ blockCount S (2 ^ j) := by
  set f : ℕ → ℝ := S.indicator fun n : ℕ => (n : ℝ) ^ (-σ) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n =>
    Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) n
  have hpart : ∀ N, ∑ n ∈ Finset.range (2 ^ N), f n =
      f 0 + ∑ j ∈ Finset.range N, ∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [← Finset.sum_range_add_sum_Ico f (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ N)), ih,
        Finset.sum_range_succ, pow_succ', add_assoc]
  have hblock : ∀ j, ∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n ≤
      (blockCount S (2 ^ j) : ℝ) * ((2 : ℝ) ^ j) ^ (-σ) := by
    intro j
    have h1 : ∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n =
        ∑ n ∈ (Finset.Ico (2 ^ j) (2 * 2 ^ j)).filter (· ∈ S), (n : ℝ) ^ (-σ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hf, Set.indicator_apply]
    rw [h1]
    have h2 := Finset.sum_le_card_nsmul ((Finset.Ico (2 ^ j) (2 * 2 ^ j)).filter (· ∈ S))
      (fun n : ℕ => (n : ℝ) ^ (-σ)) (((2 : ℝ) ^ j) ^ (-σ)) ?_
    · rw [nsmul_eq_mul] at h2
      exact h2
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
      exact_mod_cast hn.1.1
  by_contra hfreq
  rw [Filter.not_frequently] at hfreq
  have hB0 : ∀ j, 0 ≤ ∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n :=
    fun j => Finset.sum_nonneg fun n _ => hf0 n
  have hBev : ∀ᶠ j in atTop, ‖∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n‖ ≤ ((2 : ℝ) ^ (-η)) ^ j := by
    filter_upwards [hfreq] with j hj
    push Not at hj
    rw [Real.norm_eq_abs, abs_of_nonneg (hB0 j)]
    calc ∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n
        ≤ (blockCount S (2 ^ j) : ℝ) * ((2 : ℝ) ^ j) ^ (-σ) := hblock j
      _ ≤ ((2 : ℝ) ^ j) ^ (σ - η) * ((2 : ℝ) ^ j) ^ (-σ) := by
          apply mul_le_mul_of_nonneg_right hj.le (by positivity)
      _ = ((2 : ℝ) ^ j) ^ (-η) := by
          rw [← Real.rpow_add (by positivity)]; ring_nf
      _ = ((2 : ℝ) ^ (-η)) ^ j := two_pow_rpow j (-η)
  have hr0 : 0 ≤ (2 : ℝ) ^ (-η) := by positivity
  have hr1 : (2 : ℝ) ^ (-η) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hBsum : Summable fun j => ∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n :=
    Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hr0 hr1) hBev
  have hfsum : Summable f := by
    refine summable_of_sum_range_le hf0
      (c := f 0 + ∑' j, ∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n) fun N => ?_
    calc ∑ n ∈ Finset.range N, f n ≤ ∑ n ∈ Finset.range (2 ^ N), f n :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr Nat.lt_two_pow_self.le) (fun n _ _ => hf0 n)
      _ = f 0 + ∑ j ∈ Finset.range N, ∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n := hpart N
      _ ≤ f 0 + ∑' j, ∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n := by
          gcongr
          exact hBsum.sum_le_tsum _ (fun j _ => hB0 j)
  have hmem : σ ∈ {σ : ℝ | 0 ≤ σ ∧ Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-σ))} :=
    ⟨hσ0, hfsum⟩
  have hle : dim S ≤ σ := csInf_le ⟨0, fun _ h => h.1⟩ hmem
  linarith
end DeletedPrimes
