-- Prove2me | solution 1 for Erdos3.erdos_3_of_r_bound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:35:43.373184+00:00
-- url     : https://prove2.me/submissions/7e89dd52-0ed3-42fd-91e6-56d7bc7f961b

import Definitions.Def_Erdos142Basic
import Mathlib

namespace Erdos3Aux
open Erdos142

/-- If `A` has no `k`-term progression, every finite subset of `A ∩ [1, N]` has at most `r k N`
elements. -/
lemma card_le_r {A : Set ℕ} {k : ℕ} (hA : ∀ S ⊆ A, ¬ IsAPOfLength S k)
    {T : Finset ℕ} {N : ℕ} (hTA : (T : Set ℕ) ⊆ A) (hT : T ⊆ Finset.Icc 1 N) :
    T.card ≤ r k N := by
  apply le_r hT
  intro t ht hap
  exact absurd hap (hA t (ht.trans hTA))

/-- The reciprocal sum over `A ∩ [2^j, 2^(j+1))` is at most `r k (2^(j+1)) / 2^j`. -/
lemma block_sum_le {A : Set ℕ} {k : ℕ} (hA : ∀ S ⊆ A, ¬ IsAPOfLength S k) (j : ℕ) :
    (∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), A.indicator (fun n : ℕ => 1 / (n : ℝ)) n)
      ≤ (r k (2 ^ (j + 1)) : ℝ) / 2 ^ j := by
  classical
  set T : Finset ℕ := (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter (· ∈ A) with hT
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have h1 : (∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), A.indicator (fun n : ℕ => 1 / (n : ℝ)) n)
      = ∑ n ∈ T, 1 / (n : ℝ) := by
    rw [hT, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp [Set.indicator_apply]
  have h2 : ∑ n ∈ T, 1 / (n : ℝ) ≤ ∑ n ∈ T, 1 / (2 ^ j : ℝ) := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hn' := (Finset.mem_filter.mp hn).1
    have hle : (2 : ℝ) ^ j ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn').1
    exact one_div_le_one_div_of_le hpos hle
  have hcard : T.card ≤ r k (2 ^ (j + 1)) := by
    apply card_le_r hA
    · intro n hn
      exact (Finset.mem_filter.mp (Finset.mem_coe.mp hn)).2
    · intro n hn
      have hn' := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
      have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      exact Finset.mem_Icc.mpr ⟨by omega, hn'.2.le⟩
  have hcard' : (T.card : ℝ) ≤ r k (2 ^ (j + 1)) := by exact_mod_cast hcard
  rw [h1]
  refine h2.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [mul_one_div]
  exact div_le_div_of_nonneg_right hcard' hpos.le

/-- Dyadic decomposition of partial sums. -/
lemma sum_Ico_dyadic (g : ℕ → ℝ) (J : ℕ) :
    ∑ n ∈ Finset.Ico 1 (2 ^ J), g n
      = ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), g n := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact (Finset.sum_Ico_consecutive g Nat.one_le_two_pow
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J))).symm

/-- If `r k N ≤ N / (log N)^(1+c)` for large `N` and `A` has no `k`-term progression, then
`∑_{a ∈ A} 1/a` converges. -/
theorem summable_of_no_ap {A : Set ℕ} {k : ℕ} {c : ℝ} (hc : 0 < c)
    (hr : ∀ᶠ N : ℕ in Filter.atTop, (r k N : ℝ) ≤ (N : ℝ) / (Real.log N) ^ (1 + c))
    (hA : ∀ S ⊆ A, ¬ IsAPOfLength S k) :
    Summable fun a : A ↦ 1 / (a : ℝ) := by
  classical
  set g : ℕ → ℝ := A.indicator (fun n : ℕ => 1 / (n : ℝ)) with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    rw [hg, Set.indicator_apply]
    split_ifs <;> positivity
  set D : ℕ → ℝ := fun j => ∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), g n with hD
  have hD0 : ∀ j, 0 ≤ D j := fun j => Finset.sum_nonneg fun n _ => hg0 n
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hr
  set C : ℝ := 2 / (Real.log 2) ^ (1 + c) with hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the majorant
  have hmaj : Summable fun j : ℕ => C * (((j + 1 : ℕ) : ℝ) ^ (1 + c))⁻¹ := by
    have h := Real.summable_nat_rpow_inv.mpr (show (1 : ℝ) < 1 + c by linarith)
    exact ((summable_nat_add_iff 1).mpr h).mul_left C
  have hbd : ∀ j, N0 ≤ j → D j ≤ C * (((j + 1 : ℕ) : ℝ) ^ (1 + c))⁻¹ := by
    intro j hj
    have hN : N0 ≤ 2 ^ (j + 1) :=
      (hj.trans (Nat.lt_two_pow_self.le)).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h1 := hN0 _ hN
    have hlog : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) * Real.log 2 := by
      push_cast
      rw [Real.log_pow]
      push_cast
      ring
    rw [hlog] at h1
    have hj1 : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have hpos : (0 : ℝ) < 2 ^ j := by positivity
    have hb := block_sum_le hA j
    have hDj : D j ≤ (r k (2 ^ (j + 1)) : ℝ) / 2 ^ j := hb
    refine hDj.trans ?_
    calc (r k (2 ^ (j + 1)) : ℝ) / 2 ^ j
        ≤ (((2 ^ (j + 1) : ℕ) : ℝ) / (((j + 1 : ℕ) : ℝ) * Real.log 2) ^ (1 + c)) / 2 ^ j :=
          div_le_div_of_nonneg_right h1 hpos.le
      _ = C * (((j + 1 : ℕ) : ℝ) ^ (1 + c))⁻¹ := by
          rw [Real.mul_rpow hj1.le hlog2.le, hC]
          push_cast
          rw [pow_succ]
          field_simp
  have hDsum : Summable D := by
    refine Summable.of_norm_bounded_eventually hmaj ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_ge_atTop N0] with j hj
    rw [Real.norm_of_nonneg (hD0 j)]
    exact hbd j hj
  -- partial sums are bounded by `∑' D`
  have hpart : ∀ n, ∑ m ∈ Finset.range n, g m ≤ ∑' j, D j := by
    intro n
    have h1 : ∑ m ∈ Finset.range n, g m ≤ ∑ m ∈ Finset.range (2 ^ n), g m :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.lt_two_pow_self.le)) (fun i _ _ => hg0 i)
    have hg00 : g 0 = 0 := by
      rw [hg, Set.indicator_apply]
      simp
    have h2 : ∑ m ∈ Finset.range (2 ^ n), g m = ∑ j ∈ Finset.range n, D j := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.one_le_two_pow), hg00, zero_add]
      exact sum_Ico_dyadic g n
    rw [h2] at h1
    exact h1.trans (hDsum.sum_le_tsum _ fun j _ => hD0 j)
  have hgs : Summable g := summable_of_sum_range_le hg0 hpart
  exact (summable_subtype_iff_indicator (f := fun n : ℕ => 1 / (n : ℝ)) (s := A)).mpr hgs

end Erdos3Aux

open Erdos142

theorem solution
    (h : ∀ k : ℕ, 3 ≤ k → ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (r k N : ℝ) ≤ (N : ℝ) / (Real.log N) ^ (1 + c)) :
    ∀ A : Set ℕ, (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, IsAPOfLength S k := by
  intro A hA
  rw [Filter.frequently_atTop]
  intro a
  refine ⟨max a 3, le_max_left _ _, ?_⟩
  by_contra hno
  push Not at hno
  obtain ⟨c, hc, hr⟩ := h (max a 3) (le_max_right _ _)
  exact hA (Erdos3Aux.summable_of_no_ap hc hr hno)
