-- Prove2me | solution 1 for BlockCycleRotation.tsum_gTerm_ge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:45:38.511727+00:00
-- url     : https://prove2.me/submissions/81b5ae9b-70f8-41e4-8842-8ac6f14e6ac0

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Remark21
import Theorems.Thm_BlockCycleRotation_sum_inv_sq_tail_le
import Theorems.Thm_BlockCycleRotation_gTerm_eq
import Theorems.Thm_BlockCycleRotation_gTerm_row_ge
import Theorems.Thm_BlockCycleRotation_tsum_telescope_inv
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

theorem tsum_inv_sq_ge {K : ℕ} (hK : 0 < K) :
    (1 : ℝ) / (K : ℝ) ≤ ∑' j : ℕ, 1 / ((j : ℝ) + (K : ℝ)) ^ 2 := by
  have hgs : Summable (fun j : ℕ => 1 / ((j : ℝ) + (K : ℝ)) ^ 2) := by
    have h0 : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
      rw [Real.summable_one_div_nat_pow]; norm_num
    refine ((summable_nat_add_iff K).2 h0).congr fun j => ?_
    push_cast
    ring_nf
  have hnn : ∀ j : ℕ, 0 ≤ 1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1) := by
    intro j
    have h1 : (0 : ℝ) < (j : ℝ) + (K : ℝ) := by
      have : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
      positivity
    have := one_div_le_one_div_of_le h1 (by linarith : (j : ℝ) + (K : ℝ) ≤ (j : ℝ) + (K : ℝ) + 1)
    linarith
  have hle : ∀ j : ℕ, 1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1)
      ≤ 1 / ((j : ℝ) + (K : ℝ)) ^ 2 := by
    intro j
    have h1 : (0 : ℝ) < (j : ℝ) + (K : ℝ) := by
      have : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
      positivity
    have hrw : 1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1)
        = 1 / (((j : ℝ) + (K : ℝ)) * ((j : ℝ) + (K : ℝ) + 1)) := by
      field_simp
      ring
    rw [hrw]
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith
  have hs : Summable (fun j : ℕ => 1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1)) :=
    Summable.of_nonneg_of_le hnn hle hgs
  calc (1 : ℝ) / (K : ℝ)
      = ∑' j : ℕ, (1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1)) :=
        (tsum_telescope_inv hK).symm
    _ ≤ ∑' j : ℕ, 1 / ((j : ℝ) + (K : ℝ)) ^ 2 := hs.tsum_le_tsum hle hgs

end BlockCycleRotation

open BlockCycleRotation in
set_option maxHeartbeats 800000 in
-- Several tsum manipulations chained.
theorem solution :
    (∑ a ∈ Finset.range 61, ∑ a' ∈ Finset.range a, gTerm (a, a')) + (54 / 100) * (1 / 61)
      ≤ ∑' p, gTerm p:= by
  have hnn : (0 : ℕ × ℕ → ℝ) ≤ gTerm := fun p => gTerm_nonneg p
  have hrows := (summable_prod_of_nonneg hnn).1 gTerm_summable
  have hrowsum : Summable (fun a : ℕ => ∑ a' ∈ Finset.range a, gTerm (a, a')) := by
    refine hrows.2.congr fun a => ?_
    exact tsum_eq_sum (gTerm_row_support a)
  have hshift : Summable (fun j : ℕ => ∑ a' ∈ Finset.range (j + 61), gTerm (j + 61, a')) :=
    (summable_nat_add_iff (f := fun a : ℕ => ∑ a' ∈ Finset.range a, gTerm (a, a')) 61).2 hrowsum
  have hgs : Summable (fun j : ℕ => (54 / 100 : ℝ) * (1 / ((j : ℝ) + 61) ^ 2)) := by
    have h0 : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
      rw [Real.summable_one_div_nat_pow]; norm_num
    have h1 : Summable (fun j : ℕ => 1 / ((j : ℝ) + 61) ^ 2) := by
      refine ((summable_nat_add_iff 61).2 h0).congr fun j => ?_
      push_cast
      ring_nf
    exact h1.mul_left _
  have hsplit : (∑ a ∈ Finset.range 61, ∑ a' ∈ Finset.range a, gTerm (a, a'))
      + ∑' j : ℕ, (∑ a' ∈ Finset.range (j + 61), gTerm (j + 61, a'))
      = ∑' p, gTerm p := by
    rw [gTerm_eq_tsum_finRows]
    exact hrowsum.sum_add_tsum_nat_add 61
  have htail : (54 / 100 : ℝ) * (1 / 61)
      ≤ ∑' j : ℕ, (∑ a' ∈ Finset.range (j + 61), gTerm (j + 61, a')) := by
    have hterm : ∀ j : ℕ, (54 / 100 : ℝ) * (1 / ((j : ℝ) + 61) ^ 2)
        ≤ ∑ a' ∈ Finset.range (j + 61), gTerm (j + 61, a') := by
      intro j
      have h := gTerm_row_ge (a := j + 61) (by omega)
      have hcast : ((j + 61 : ℕ) : ℝ) = (j : ℝ) + 61 := by push_cast; ring
      rw [hcast] at h
      calc (54 / 100 : ℝ) * (1 / ((j : ℝ) + 61) ^ 2)
          = (54 / 100 : ℝ) / ((j : ℝ) + 61) ^ 2 := by ring
        _ ≤ _ := h
    have hK := tsum_inv_sq_ge (K := 61) (by norm_num)
    have hcast61 : ((61 : ℕ) : ℝ) = 61 := by norm_num
    rw [hcast61] at hK
    have h1 : (54 / 100 : ℝ) * (1 / 61) ≤ (54 / 100 : ℝ) * ∑' j : ℕ, 1 / ((j : ℝ) + 61) ^ 2 :=
      mul_le_mul_of_nonneg_left hK (by norm_num)
    have h2 : (54 / 100 : ℝ) * ∑' j : ℕ, 1 / ((j : ℝ) + 61) ^ 2
        = ∑' j : ℕ, (54 / 100 : ℝ) * (1 / ((j : ℝ) + 61) ^ 2) := tsum_mul_left.symm
    rw [h2] at h1
    exact le_trans h1 (hgs.tsum_le_tsum hterm hshift)
  rw [← hsplit]
  exact add_le_add_right htail _
