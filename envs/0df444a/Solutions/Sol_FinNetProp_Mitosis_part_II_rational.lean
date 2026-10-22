-- Prove2me | solution 1 for FinNetProp.Mitosis.part_II_rational
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T16:13:18.65803+00:00
-- url     : https://prove2.me/submissions/03308f37-3e94-4ebb-b9c7-b12b2af5d0f9

import Mathlib
import Definitions.Def_FinNetProp_Mitosis_Setting
import Theorems.Thm_FinNetProp_Mitosis_lemma_A_1

namespace FinNetProp.Mitosis

open Finset

lemma fnpR_ratio (x y : ℚ) (hx : 0 < x) (hy : 0 < y) :
    ∃ q r : ℕ, 0 < q ∧ 0 < r ∧ (x : ℝ) = ((q : ℝ) / (r : ℝ)) * (y : ℝ) := by
  set ρ : ℚ := x / y with hρ
  have hρpos : 0 < ρ := div_pos hx hy
  refine ⟨ρ.num.toNat, ρ.den, ?_, ρ.den_pos, ?_⟩
  · have := Rat.num_pos.2 hρpos; omega
  · have hnum : ((ρ.num.toNat : ℕ) : ℝ) = (ρ.num : ℝ) := by
      have := Rat.num_pos.2 hρpos
      have h' : ((ρ.num.toNat : ℕ) : ℤ) = ρ.num := Int.toNat_of_nonneg this.le
      exact_mod_cast h'
    rw [hnum]
    have hc : ((ρ.num : ℝ) / (ρ.den : ℝ)) = (ρ : ℝ) := by
      rw [Rat.cast_def]
    rw [hc, hρ]
    push_cast
    field_simp [hy.ne']

theorem fnp_part_II_rational (b : BankruptcyRule) (hcb : ClaimsBounded b)
    (hll : LimitedLiability b) (hpc : PriorityOfCreditors b) (himp : Impartial b)
    (hmit : InvariantToMitosis b) (F : FinNet) (hF : RationalLiabilities F) :
    IsPropSolution F (b F) := by
  refine ⟨b.mem F, ?_⟩
  intro i hi j hj
  have hnn : ∀ a c, 0 ≤ b F a c := (b.mem F).1
  by_cases hL0 : F.L i j = 0
  · have h1 := hcb F i hi j hj
    rw [hL0] at h1 ⊢
    have : relLiab F i j = 0 := by simp [relLiab, hL0]
    rw [this, zero_mul, min_self]
    exact le_antisymm h1 (hnn i j)
  have hLpos : 0 < F.L i j := lt_of_le_of_ne (F.L_nonneg i j) (Ne.symm hL0)
  set Lbar := ∑ k ∈ F.N, F.L i k with hLbar
  have hLbarpos : 0 < Lbar :=
    lt_of_lt_of_le hLpos (Finset.single_le_sum (fun k _ => F.L_nonneg i k) hj)
  have hrel : relLiab F i j = F.L i j / Lbar := by simp [relLiab, hL0, hLbar]
  set a := F.z i + ∑ k ∈ F.N, b F k i with ha
  have heq_a : equity F (b F) i = a - ∑ k ∈ F.N, b F i k := rfl
  rw [hrel]
  by_cases hcase : Lbar ≤ a
  · -- Case A.5(a)
    have hbij : b F i j = F.L i j := by
      by_contra hne
      have hlt : b F i j < F.L i j := lt_of_le_of_ne (hcb F i hi j hj) hne
      have hrow : RowLt F.N (b F) F.L i := ⟨fun k hk => hcb F i hi k hk, j, hj, hlt⟩
      have he := hpc F i hi hrow
      have hslt : ∑ k ∈ F.N, b F i k < Lbar :=
        Finset.sum_lt_sum (fun k hk => hcb F i hi k hk) ⟨j, hj, hlt⟩
      rw [heq_a] at he
      linarith
    rw [hbij]
    symm; apply min_eq_right
    rw [div_mul_eq_mul_div, le_div_iff₀ hLbarpos]
    exact mul_le_mul_of_nonneg_left hcase hLpos.le
  · -- Case A.5(b)
    push Not at hcase
    -- (A.5): b_ik = r_i L_ik
    set ri := b F i j / F.L i j with hri
    have hprop : ∀ k ∈ F.N, b F i k = ri * F.L i k := by
      intro k hk
      by_cases hk0 : F.L i k = 0
      · have := himp F i hi k hk i hi (by rw [hk0, F.L_diag])
        rw [this, (b.mem F).2.1 i, hk0, mul_zero]
      have hkpos : 0 < F.L i k := lt_of_le_of_ne (F.L_nonneg i k) (Ne.symm hk0)
      obtain ⟨x, hx⟩ := hF i k
      obtain ⟨y, hy⟩ := hF i j
      have hx0 : (0 : ℚ) < x := by exact_mod_cast (hx ▸ hkpos)
      have hy0 : (0 : ℚ) < y := by exact_mod_cast (hy ▸ hLpos)
      obtain ⟨q, r, hq, hr, hqr⟩ := fnpR_ratio x y hx0 hy0
      have hLL : F.L i k = ((q : ℝ) / (r : ℝ)) * F.L i j := by rw [hx, hy]; exact hqr
      have hA := lemma_A_1 b himp hmit F i k j hi hk hj q r hq hr hLL
      rw [hA, hLL, hri]
      field_simp
    -- (A.7) with equality
    have hle : ∑ k ∈ F.N, b F i k ≤ a := by
      have := hll F i hi; rw [heq_a] at this; linarith
    have hsum : ∑ k ∈ F.N, b F i k = a := by
      by_contra hne
      have hlt : ∑ k ∈ F.N, b F i k < a := lt_of_le_of_ne hle hne
      have hnotrow : ¬ RowLt F.N (b F) F.L i := by
        intro hrow
        have := hpc F i hi hrow
        rw [heq_a] at this; linarith
      have hall : ∀ k ∈ F.N, b F i k = F.L i k := by
        intro k hk
        by_contra hk'
        exact hnotrow ⟨fun l hl => hcb F i hi l hl, k, hk,
          lt_of_le_of_ne (hcb F i hi k hk) hk'⟩
      rw [Finset.sum_congr rfl hall] at hlt
      linarith
    have hsum2 : ∑ k ∈ F.N, b F i k = ri * Lbar := by
      rw [Finset.sum_congr rfl hprop, ← Finset.mul_sum]
    have hriv : ri = a / Lbar := by
      rw [eq_div_iff hLbarpos.ne', ← hsum2, hsum]
    rw [hprop j hj, hriv]
    have hval : a / Lbar * F.L i j = F.L i j / Lbar * a := by ring
    rw [hval]
    symm; apply min_eq_left
    rw [div_mul_eq_mul_div, div_le_iff₀ hLbarpos]
    exact mul_le_mul_of_nonneg_left hcase.le hLpos.le

end FinNetProp.Mitosis

theorem solution (b : FinNetProp.Mitosis.BankruptcyRule) (hcb : FinNetProp.Mitosis.ClaimsBounded b)
    (hll : FinNetProp.Mitosis.LimitedLiability b) (hpc : FinNetProp.Mitosis.PriorityOfCreditors b)
    (himp : FinNetProp.Mitosis.Impartial b)
    (hmit : FinNetProp.Mitosis.InvariantToMitosis b) (F : FinNetProp.Mitosis.FinNet)
    (hF : FinNetProp.Mitosis.RationalLiabilities F) :
    FinNetProp.Mitosis.IsPropSolution F (b F) :=
  FinNetProp.Mitosis.fnp_part_II_rational b hcb hll hpc himp hmit F hF
