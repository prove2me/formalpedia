-- Prove2me | solution 1 for BlockCycleRotation.euler_zeta21
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:38:10.120066+00:00
-- url     : https://prove2.me/submissions/b36cf1e4-5bc8-456e-b9e4-d146178d04c3

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Remark21
import Theorems.Thm_BlockCycleRotation_sum_inv_sq_tail_le
import Theorems.Thm_BlockCycleRotation_tsum_tail_inv_sq
import Theorems.Thm_BlockCycleRotation_tsum_pTerm
import Theorems.Thm_BlockCycleRotation_qTerm_row
import Mathlib

open Real Finset Filter Topology

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem zTerm_nonneg (p : ℕ × ℕ) : 0 ≤ zTerm p := by
  unfold zTerm; split
  · positivity
  · exact le_refl 0

theorem zTerm_col_sum_le (a' : ℕ) (s : Finset ℕ) :
    ∑ a ∈ s, zTerm (a, a') ≤ 1 / (a' : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos a' with rfl | ha'
  · simp [zTerm]
  · have ha'R : (0 : ℝ) < (a' : ℝ) := by exact_mod_cast ha'
    have h1 : ∑ a ∈ s, zTerm (a, a')
        = ∑ a ∈ s.filter (fun a => a' < a), (1 / (a' : ℝ)) * (1 / (a : ℝ) ^ 2) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun a _ => ?_
      unfold zTerm
      by_cases h : a' < a
      · rw [if_pos ⟨ha', h⟩, if_pos h]
        field_simp
      · rw [if_neg (by tauto), if_neg h]
    rw [h1, ← Finset.mul_sum]
    have h3 := sum_inv_sq_tail_le ha' (s.filter (fun a => a' < a))
      (fun a ha => (Finset.mem_filter.1 ha).2)
    calc (1 / (a' : ℝ)) * ∑ a ∈ s.filter (fun a => a' < a), 1 / (a : ℝ) ^ 2
        ≤ (1 / (a' : ℝ)) * (1 / (a' : ℝ)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 1 / (a' : ℝ) ^ 2 := by ring

theorem zTerm_col_summable (a' : ℕ) : Summable (fun a => zTerm (a, a')) :=
  summable_of_sum_le (fun a => zTerm_nonneg (a, a')) (zTerm_col_sum_le a')

theorem zTerm_col_tsum_le (a' : ℕ) : ∑' a, zTerm (a, a') ≤ 1 / (a' : ℝ) ^ 2 :=
  Real.tsum_le_of_sum_le (fun a => zTerm_nonneg (a, a')) (zTerm_col_sum_le a')

theorem zTerm_summable : Summable zTerm := by
  refine (Equiv.prodComm ℕ ℕ).summable_iff.1 ?_
  change Summable (fun q : ℕ × ℕ => zTerm (q.2, q.1))
  have hnn : (0 : ℕ × ℕ → ℝ) ≤ fun q => zTerm (q.2, q.1) := fun q => zTerm_nonneg _
  rw [summable_prod_of_nonneg hnn]
  refine ⟨fun a' => zTerm_col_summable a', ?_⟩
  have hg : Summable (fun a' : ℕ => 1 / (a' : ℝ) ^ 2) := by
    rw [Real.summable_one_div_nat_pow]; norm_num
  refine Summable.of_nonneg_of_le (fun a' => ?_) (fun a' => zTerm_col_tsum_le a') hg
  exact tsum_nonneg fun a => zTerm_nonneg _

theorem harm_succ {a : ℕ} (ha : 1 ≤ a) : harm (a + 1) = harm a + 1 / (a : ℝ) := by
  unfold harm
  rw [Finset.sum_Ico_succ_top ha]

theorem pTerm_pos (q : ℕ × ℕ) : 0 < pTerm q := by
  unfold pTerm; positivity

theorem pTerm_row_summable (i : ℕ) : Summable (fun j => pTerm (i, j)) := by
  have hg : Summable (fun j : ℕ => 1 / (((i : ℝ) + 1) * ((j : ℝ) + 1) ^ 2)) := by
    have h : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
      have h0 : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
        rw [Real.summable_one_div_nat_pow]; norm_num
      refine ((summable_nat_add_iff 1).2 h0).congr fun j => ?_
      push_cast; ring
    refine (h.mul_left (1 / ((i : ℝ) + 1))).congr fun j => ?_
    field_simp
  refine Summable.of_nonneg_of_le (fun j => (pTerm_pos _).le) (fun j => ?_) hg
  unfold pTerm
  refine one_div_le_one_div_of_le (by positivity) ?_
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have h1 : ((j : ℝ) + 1) ^ 2 ≤ (((i : ℝ) + 1) + ((j : ℝ) + 1)) ^ 2 := by nlinarith
  have h2 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  nlinarith

theorem pTerm_row_tsum_le (i : ℕ) : ∑' j, pTerm (i, j) ≤ 1 / ((i : ℝ) + 1) ^ 2 := by
  have hi : 0 < i + 1 := by omega
  have heq : ∀ j : ℕ, pTerm (i, j)
      = (1 / ((i : ℝ) + 1)) * (1 / (((i + 1 : ℕ) : ℝ) + (j : ℝ) + 1) ^ 2) := by
    intro j
    unfold pTerm
    push_cast
    field_simp
    ring
  rw [tsum_congr heq, tsum_mul_left]
  have ht := tsum_tail_inv_sq hi
  have hpos : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
  calc (1 / ((i : ℝ) + 1)) * ∑' j : ℕ, 1 / (((i + 1 : ℕ) : ℝ) + (j : ℝ) + 1) ^ 2
      ≤ (1 / ((i : ℝ) + 1)) * (1 / ((i + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
    _ = 1 / ((i : ℝ) + 1) ^ 2 := by
        have hc : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
        rw [hc]
        field_simp

theorem pTerm_summable : Summable pTerm := by
  have hnn : (0 : ℕ × ℕ → ℝ) ≤ pTerm := fun q => (pTerm_pos q).le
  rw [summable_prod_of_nonneg hnn]
  refine ⟨pTerm_row_summable, ?_⟩
  have hg : Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) := by
    have h0 : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
      rw [Real.summable_one_div_nat_pow]; norm_num
    refine ((summable_nat_add_iff 1).2 h0).congr fun j => ?_
    push_cast; ring
  exact Summable.of_nonneg_of_le (fun i => tsum_nonneg fun j => (pTerm_pos _).le)
    pTerm_row_tsum_le hg

/-- **The key identity.**  `1/(n(n+k)²) + 1/(k(n+k)²) = 1/(n·k·(n+k))`. -/
theorem pTerm_add_swap (q : ℕ × ℕ) : pTerm q + pTerm (q.2, q.1) = qTerm q := by
  have h1 : (0 : ℝ) < (q.1 : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (q.2 : ℝ) + 1 := by positivity
  unfold pTerm qTerm
  field_simp
  ring

theorem pTerm_swap_summable : Summable (fun q : ℕ × ℕ => pTerm (q.2, q.1)) :=
  (Equiv.prodComm ℕ ℕ).summable_iff.2 pTerm_summable

theorem tsum_pTerm_swap : ∑' q : ℕ × ℕ, pTerm (q.2, q.1) = ∑' q : ℕ × ℕ, pTerm q :=
  (Equiv.prodComm ℕ ℕ).tsum_eq pTerm

theorem qTerm_summable : Summable qTerm :=
  (pTerm_summable.add pTerm_swap_summable).congr fun q => pTerm_add_swap q

/-- **The swap symmetry gives `2·ζ(2,1)`.** -/
theorem tsum_qTerm_eq_two : ∑' q : ℕ × ℕ, qTerm q = 2 * zeta21 := by
  have h : ∑' q : ℕ × ℕ, qTerm q = (∑' q : ℕ × ℕ, pTerm q) + ∑' q : ℕ × ℕ, pTerm (q.2, q.1) := by
    rw [← Summable.tsum_add pTerm_summable pTerm_swap_summable]
    exact tsum_congr fun q => (pTerm_add_swap q).symm
  rw [h, tsum_pTerm_swap, zeta21, tsum_pTerm]
  ring

theorem tsum_qTerm_rows :
    ∑' q : ℕ × ℕ, qTerm q = ∑' i : ℕ, harm (i + 2) / ((i : ℝ) + 1) ^ 2 := by
  rw [qTerm_summable.tsum_prod]
  exact tsum_congr qTerm_row

theorem zTerm_row (a : ℕ) : ∑' a' : ℕ, zTerm (a, a') = harm a / (a : ℝ) ^ 2 := by
  have hsupp : ∀ a' ∉ Finset.range a, zTerm (a, a') = 0 := by
    intro a' ha'
    simp only [Finset.mem_range, not_lt] at ha'
    unfold zTerm
    rw [if_neg]
    rintro ⟨-, h2⟩
    omega
  rw [tsum_eq_sum hsupp]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [harm]
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot ha]
    have h0 : zTerm (a, 0) = 0 := by
      unfold zTerm; rw [if_neg]; rintro ⟨h1, -⟩; omega
    rw [h0, zero_add]
    unfold harm
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun a' ha' => ?_
    rw [Finset.mem_Ico] at ha'
    have ha'0 : (0 : ℝ) < (a' : ℝ) := by
      have : 0 < a' := by omega
      exact_mod_cast this
    have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    unfold zTerm
    rw [if_pos ⟨by omega, by omega⟩]
    field_simp

theorem harmRow_summable : Summable (fun a : ℕ => harm a / (a : ℝ) ^ 2) := by
  have hnn : (0 : ℕ × ℕ → ℝ) ≤ zTerm := fun p => zTerm_nonneg p
  have h := (summable_prod_of_nonneg hnn).1 zTerm_summable
  exact h.2.congr fun a => zTerm_row a

theorem zeta21_eq : zeta21 = ∑' a : ℕ, harm a / (a : ℝ) ^ 2 := by
  rw [zeta21, zTerm_summable.tsum_prod]
  exact tsum_congr zTerm_row

theorem inv_cube_summable : Summable (fun a : ℕ => 1 / (a : ℝ) ^ 3) := by
  rw [Real.summable_one_div_nat_pow]; norm_num

theorem zeta3_eq : zeta3 = ∑' a : ℕ, 1 / (a : ℝ) ^ 3 := by
  have hshift : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ)) : ℝ) ^ 3) :=
    (summable_nat_add_iff 1).2 inv_cube_summable
  have h1 : ∑' a : ℕ, 1 / (a : ℝ) ^ 3
      = 1 / (((0 : ℕ)) : ℝ) ^ 3 + ∑' n : ℕ, 1 / (((n + 1 : ℕ)) : ℝ) ^ 3 :=
    tsum_eq_zero_add' hshift
  have h2 : (1 : ℝ) / (((0 : ℕ)) : ℝ) ^ 3 = 0 := by norm_num
  have h3 : ∑' n : ℕ, 1 / (((n + 1 : ℕ)) : ℝ) ^ 3 = zeta3 := by
    rw [zeta3]
    exact tsum_congr fun n => by push_cast; ring
  rw [h1, h2, h3, zero_add]

end BlockCycleRotation

open BlockCycleRotation in
/-- **Euler's `ζ(2,1) = ζ(3)`.** -/
theorem solution : zeta21 = zeta3:= by
  have hsum : Summable (fun a : ℕ => harm a / (a : ℝ) ^ 2 + 1 / (a : ℝ) ^ 3) :=
    harmRow_summable.add inv_cube_summable
  have hrow : ∑' q : ℕ × ℕ, qTerm q = zeta21 + zeta3 := by
    rw [tsum_qTerm_rows, zeta21_eq, zeta3_eq,
      ← Summable.tsum_add harmRow_summable inv_cube_summable,
      tsum_eq_zero_add' ((summable_nat_add_iff 1).2 hsum)]
    have hzero : harm 0 / ((0 : ℕ) : ℝ) ^ 2 + 1 / ((0 : ℕ) : ℝ) ^ 3 = 0 := by
      simp [harm]
    rw [hzero, zero_add]
    refine tsum_congr fun i => ?_
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hc : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    rw [hc, harm_succ (by omega : 1 ≤ i + 1), hc]
    field_simp
  have h2 := tsum_qTerm_eq_two
  rw [hrow] at h2
  linarith
