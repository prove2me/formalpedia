-- Prove2me | solution 1 for BlockCycleRotation.tsum_gTerm_le_partial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:40:32.948934+00:00
-- url     : https://prove2.me/submissions/f17980f4-d2a0-4645-a3a1-149b2bfacc2b

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Remark21
import Theorems.Thm_BlockCycleRotation_sum_inv_sq_tail_le
import Theorems.Thm_BlockCycleRotation_gTerm_eq
import Theorems.Thm_BlockCycleRotation_gTerm_row_le
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

theorem gTerm_nonneg (p : ℕ × ℕ) : 0 ≤ gTerm p := by
  unfold gTerm; split
  · positivity
  · exact le_refl 0

theorem zTerm_nonneg (p : ℕ × ℕ) : 0 ≤ zTerm p := by
  unfold zTerm; split
  · positivity
  · exact le_refl 0

theorem eTerm_nonneg (p : ℕ × ℕ) : 0 ≤ eTerm p := by
  unfold eTerm; split
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

theorem eTerm_le_zTerm (p : ℕ × ℕ) : eTerm p ≤ zTerm p := by
  unfold eTerm zTerm
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have ha' : (0 : ℝ) < (p.2 : ℝ) := by
      have : 0 < p.2 := by omega
      exact_mod_cast this
    have ha : (0 : ℝ) < (p.1 : ℝ) := by
      have : 0 < p.1 := by omega
      exact_mod_cast this
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [mul_nonneg ha'.le (mul_nonneg ha.le ha'.le),
      mul_nonneg ha'.le (mul_nonneg ha'.le ha'.le)]
  · exact le_refl 0

theorem eTerm_summable : Summable eTerm :=
  zTerm_summable.of_nonneg_of_le eTerm_nonneg eTerm_le_zTerm

theorem gTerm_summable : Summable gTerm := by
  have h : gTerm = fun p => (zTerm p - eTerm p) / 2 := funext gTerm_eq
  rw [h]
  exact (zTerm_summable.sub eTerm_summable).div_const 2

theorem gTerm_row_support (a a' : ℕ) (h : a' ∉ Finset.range a) : gTerm (a, a') = 0 := by
  simp only [Finset.mem_range, not_lt] at h
  unfold gTerm
  rw [if_neg]
  rintro ⟨-, h2⟩
  omega

theorem gTerm_eq_tsum_finRows :
    ∑' p, gTerm p = ∑' a : ℕ, ∑ a' ∈ Finset.range a, gTerm (a, a') := by
  rw [gTerm_summable.tsum_prod]
  exact tsum_congr fun a => tsum_eq_sum (gTerm_row_support a)

end BlockCycleRotation

open BlockCycleRotation in
/-- **Truncating the all-pairs sum at `a ≤ N` loses at most `5/(8N)`.** -/
theorem solution {N : ℕ} (hN : 0 < N) :
    ∑' p, gTerm p
      ≤ (∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a, gTerm (a, a'))
        + 5 / (8 * (N : ℝ)):= by
  rw [gTerm_eq_tsum_finRows]
  refine Real.tsum_le_of_sum_le
    (fun a => Finset.sum_nonneg fun a' _ => gTerm_nonneg _) fun s => ?_
  classical
  have hsplit : ∑ a ∈ s, (∑ a' ∈ Finset.range a, gTerm (a, a'))
      = (∑ a ∈ s.filter (fun a => a ≤ N), ∑ a' ∈ Finset.range a, gTerm (a, a'))
        + ∑ a ∈ s.filter (fun a => ¬ a ≤ N), ∑ a' ∈ Finset.range a, gTerm (a, a') :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hlow : (∑ a ∈ s.filter (fun a => a ≤ N), ∑ a' ∈ Finset.range a, gTerm (a, a'))
      ≤ ∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a, gTerm (a, a') := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun a _ _ => Finset.sum_nonneg fun a' _ => gTerm_nonneg _)
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    omega
  have hhigh : (∑ a ∈ s.filter (fun a => ¬ a ≤ N), ∑ a' ∈ Finset.range a, gTerm (a, a'))
      ≤ 5 / (8 * (N : ℝ)) := by
    have h1 : (∑ a ∈ s.filter (fun a => ¬ a ≤ N), ∑ a' ∈ Finset.range a, gTerm (a, a'))
        ≤ ∑ a ∈ s.filter (fun a => ¬ a ≤ N), 5 / (8 * (a : ℝ) ^ 2) :=
      Finset.sum_le_sum fun a _ => gTerm_row_le a
    have h2 : (∑ a ∈ s.filter (fun a => ¬ a ≤ N), 5 / (8 * (a : ℝ) ^ 2))
        = (5 / 8) * ∑ a ∈ s.filter (fun a => ¬ a ≤ N), 1 / ((a : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [div_mul_eq_mul_div, mul_one_div]
      ring_nf
    have h3 : (∑ a ∈ s.filter (fun a => ¬ a ≤ N), 1 / ((a : ℝ) ^ 2)) ≤ 1 / (N : ℝ) := by
      refine sum_inv_sq_tail_le hN _ fun a ha => ?_
      simp only [Finset.mem_filter] at ha
      omega
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [h2] at h1
    have heq : (5 / 8 : ℝ) * (1 / (N : ℝ)) = 5 / (8 * (N : ℝ)) := by field_simp
    nlinarith [h1, h3]
  rw [hsplit]
  linarith
