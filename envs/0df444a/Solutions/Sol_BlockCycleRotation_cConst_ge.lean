-- Prove2me | solution 1 for BlockCycleRotation.cConst_ge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:23:36.116218+00:00
-- url     : https://prove2.me/submissions/21a3163f-99a6-47b6-be90-e452ab82f719

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Remark21
import Theorems.Thm_BlockCycleRotation_cTerm_summable
import Theorems.Thm_BlockCycleRotation_sum_inv_sq_tail_le
import Theorems.Thm_BlockCycleRotation_gTerm_eq
import Theorems.Thm_BlockCycleRotation_tsum_gTerm_eq
import Theorems.Thm_BlockCycleRotation_zeta3_le
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

theorem cTerm_nonneg (p : ℕ × ℕ) : 0 ≤ cTerm p := by
  unfold cTerm
  split
  · positivity
  · exact le_refl 0

theorem cConst_nonneg : 0 ≤ cConst :=
  tsum_nonneg fun p => cTerm_nonneg p

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

/-- **The sum over all pairs.** -/
theorem tsum_gTerm : ∑' p, gTerm p = (zeta21 - sConst) / 2 := by
  rw [zeta21, sConst]
  calc ∑' p, gTerm p = ∑' p : ℕ × ℕ, (zTerm p - eTerm p) / 2 := tsum_congr gTerm_eq
    _ = (∑' p : ℕ × ℕ, (zTerm p - eTerm p)) / 2 := tsum_div_const
    _ = (∑' p : ℕ × ℕ, zTerm p - ∑' p : ℕ × ℕ, eTerm p) / 2 := by
        rw [Summable.tsum_sub zTerm_summable eTerm_summable]

theorem uTerm_pos (d : ℕ) : 0 < uTerm d := by
  unfold uTerm; positivity

theorem uTerm_summable : Summable uTerm := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) := by
    rw [Real.summable_one_div_nat_pow]; norm_num
  refine ((summable_nat_add_iff 1).2 h).congr fun d => ?_
  unfold uTerm
  push_cast
  ring

theorem tsum_uTerm : ∑' d, uTerm d = zeta3 := rfl

/-- **Step 2, assembled.**  `ζ(3)·C = (ζ(2,1) - S)/2`. -/
theorem zeta3_mul_cConst : zeta3 * cConst = (zeta21 - sConst) / 2 := by
  have hprod : Summable (fun q : ℕ × (ℕ × ℕ) => uTerm q.1 * cTerm q.2) :=
    uTerm_summable.mul_of_nonneg cTerm_summable (fun d => (uTerm_pos d).le) cTerm_nonneg
  rw [← tsum_uTerm, cConst, Summable.tsum_mul_tsum uTerm_summable cTerm_summable hprod,
    ← tsum_gTerm_eq, tsum_gTerm]

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

set_option maxHeartbeats 10000000 in
-- 1770 rational terms again.
theorem gTerm_partial_ge :
    (2443 : ℝ) / 10000 ≤ ∑ a ∈ Finset.range 61, ∑ a' ∈ Finset.range a, gTerm (a, a') := by
  norm_num [gTerm, Finset.sum_range_succ]

end BlockCycleRotation

open BlockCycleRotation in
/-- **`C ≥ 0.2025`.** -/
theorem solution : (2025 : ℝ) / 10000 ≤ cConst:= by
  have hnn : (0 : ℕ × ℕ → ℝ) ≤ gTerm := fun p => gTerm_nonneg p
  have hrows := (summable_prod_of_nonneg hnn).1 gTerm_summable
  have hrowsum : Summable (fun a : ℕ => ∑ a' ∈ Finset.range a, gTerm (a, a')) := by
    refine hrows.2.congr fun a => ?_
    exact tsum_eq_sum (gTerm_row_support a)
  have hpartial : (∑ a ∈ Finset.range 61, ∑ a' ∈ Finset.range a, gTerm (a, a'))
      ≤ ∑' p, gTerm p := by
    rw [gTerm_eq_tsum_finRows]
    exact hrowsum.sum_le_tsum _ (fun a _ => Finset.sum_nonneg fun a' _ => gTerm_nonneg _)
  have hG : zeta3 * cConst = ∑' p, gTerm p := by
    rw [zeta3_mul_cConst, tsum_gTerm]
  have hlow : (2443 : ℝ) / 10000 ≤ zeta3 * cConst := by
    rw [hG]
    linarith [gTerm_partial_ge]
  have hup : zeta3 * cConst ≤ (12023 / 10000 : ℝ) * cConst :=
    mul_le_mul_of_nonneg_right zeta3_le cConst_nonneg
  nlinarith [hlow, hup]
