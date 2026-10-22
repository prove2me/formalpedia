-- Prove2me | solution 1 for FinNetProp.Mitosis.eisenberg_noe_unique
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T16:02:06.175043+00:00
-- url     : https://prove2.me/submissions/6b66ceeb-6e0e-4be7-9a44-93d96b54e66d

import Mathlib
import Definitions.Def_FinNetProp_Mitosis_Setting

namespace FinNetProp.Mitosis

open Finset

lemma fnp_relLiab_nonneg (F : FinNet) (i j : ℕ) : 0 ≤ relLiab F i j := by
  unfold relLiab
  split_ifs
  · exact le_rfl
  · exact div_nonneg (F.L_nonneg i j) (Finset.sum_nonneg fun k _ => F.L_nonneg i k)

lemma fnp_rowsum_nonneg (F : FinNet) (i : ℕ) : 0 ≤ ∑ k ∈ F.N, F.L i k :=
  Finset.sum_nonneg fun k _ => F.L_nonneg i k

lemma fnp_L_eq_zero_of_rowsum (F : FinNet) (i j : ℕ) (h : ∑ k ∈ F.N, F.L i k = 0) :
    F.L i j = 0 := by
  by_cases hj : j ∈ F.N
  · exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => F.L_nonneg i k)).1 h j hj
  · exact F.L_out i j (Or.inr hj)

lemma fnp_relLiab_mul (F : FinNet) (i j : ℕ) :
    relLiab F i j * ∑ k ∈ F.N, F.L i k = F.L i j := by
  unfold relLiab
  split_ifs with h
  · simp [h]
  · have hpos : (∑ k ∈ F.N, F.L i k) ≠ 0 := by
      intro h0; exact h (fnp_L_eq_zero_of_rowsum F i j h0)
    field_simp

lemma fnp_relLiab_rowsum (F : FinNet) (i : ℕ) :
    ∑ j ∈ F.N, relLiab F i j = if ∑ k ∈ F.N, F.L i k = 0 then 0 else 1 := by
  split_ifs with h
  · apply Finset.sum_eq_zero
    intro j _
    simp [relLiab, fnp_L_eq_zero_of_rowsum F i j h]
  · have : ∀ j ∈ F.N, relLiab F i j = F.L i j / ∑ k ∈ F.N, F.L i k := by
      intro j _
      unfold relLiab
      split_ifs with hj
      · simp [hj]
      · rfl
    rw [Finset.sum_congr rfl this, ← Finset.sum_div, div_self h]

lemma fnp_relLiab_rowsum_le (F : FinNet) (i : ℕ) : ∑ j ∈ F.N, relLiab F i j ≤ 1 := by
  rw [fnp_relLiab_rowsum]; split_ifs <;> norm_num

lemma fnp_min_eq (F : FinNet) (i j : ℕ) (a : ℝ) :
    min (relLiab F i j * a) (F.L i j) = relLiab F i j * min a (∑ k ∈ F.N, F.L i k) := by
  rw [mul_min_of_nonneg _ _ (fnp_relLiab_nonneg F i j), fnp_relLiab_mul]

lemma fnp_z_nonneg (F : FinNet) (i : ℕ) : 0 ≤ F.z i := by
  by_cases h : i ∈ F.N
  · exact (F.z_pos i h).le
  · exact (F.z_out i h).ge

/-- Structure of a solution of (2.1): row totals `x`. -/
lemma fnp_sol_struct (F : FinNet) (P : ℕ → ℕ → ℝ) (hP : IsPropSolution F P) :
    (∀ i ∈ F.N, ∀ j ∈ F.N, P i j = relLiab F i j * ∑ l ∈ F.N, P i l) ∧
    (∀ i ∈ F.N, ∑ l ∈ F.N, P i l =
      min (F.z i + ∑ k ∈ F.N, relLiab F k i * ∑ l ∈ F.N, P k l) (∑ k ∈ F.N, F.L i k)) := by
  obtain ⟨⟨hnn, _, _⟩, heq⟩ := hP
  -- y_i = min (a_i) (Lbar_i)
  have hrow : ∀ i ∈ F.N, ∑ l ∈ F.N, P i l =
      min (F.z i + ∑ k ∈ F.N, P k i) (∑ k ∈ F.N, F.L i k) := by
    intro i hi
    have h1 : ∀ l ∈ F.N, P i l = relLiab F i l *
        min (F.z i + ∑ k ∈ F.N, P k i) (∑ k ∈ F.N, F.L i k) := by
      intro l hl; rw [heq i hi l hl, fnp_min_eq]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, fnp_relLiab_rowsum]
    split_ifs with h
    · rw [h, zero_mul]
      have : 0 ≤ F.z i + ∑ k ∈ F.N, P k i :=
        add_nonneg (fnp_z_nonneg F i) (Finset.sum_nonneg fun k _ => hnn k i)
      exact (min_eq_right this).symm
    · rw [one_mul]
  have hform : ∀ i ∈ F.N, ∀ j ∈ F.N, P i j = relLiab F i j * ∑ l ∈ F.N, P i l := by
    intro i hi j hj
    rw [hrow i hi, heq i hi j hj, fnp_min_eq]
  refine ⟨hform, ?_⟩
  intro i hi
  rw [hrow i hi]
  congr 2
  exact Finset.sum_congr rfl fun k hk => hform k hk i hi

/-- Uniqueness of fixed points of the row-total map (the core of Eisenberg–Noe). -/
lemma fnp_fix_le (F : FinNet) (x y : ℕ → ℝ) (hx0 : ∀ i ∈ F.N, 0 ≤ x i)
    (hx : ∀ i ∈ F.N, x i = min (F.z i + ∑ k ∈ F.N, relLiab F k i * x k) (∑ k ∈ F.N, F.L i k))
    (hy : ∀ i ∈ F.N, y i = min (F.z i + ∑ k ∈ F.N, relLiab F k i * y k) (∑ k ∈ F.N, F.L i k)) :
    ∀ i ∈ F.N, y i ≤ x i := by
  classical
  by_contra hcon
  push Not at hcon
  set S := F.N.filter (fun i => x i < y i) with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨i, hi, hlt⟩ := hcon
    exact ⟨i, Finset.mem_filter.2 ⟨hi, hlt⟩⟩
  have hSsub : S ⊆ F.N := Finset.filter_subset _ _
  set c : ℕ → ℝ := fun k => ∑ i ∈ S, relLiab F k i with hc
  have hc1 : ∀ k, c k ≤ 1 := by
    intro k
    calc c k ≤ ∑ i ∈ F.N, relLiab F k i :=
          Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun i _ _ => fnp_relLiab_nonneg F k i)
      _ ≤ 1 := fnp_relLiab_rowsum_le F k
  have hc0 : ∀ k, 0 ≤ c k := fun k => Finset.sum_nonneg fun i _ => fnp_relLiab_nonneg F k i
  -- for i ∈ S, x i equals the first argument
  have hxS : ∀ i ∈ S, x i = F.z i + ∑ k ∈ F.N, relLiab F k i * x k := by
    intro i hiS
    obtain ⟨hi, hlt⟩ := Finset.mem_filter.1 hiS
    have hyle : y i ≤ ∑ k ∈ F.N, F.L i k := by rw [hy i hi]; exact min_le_right _ _
    have hxlt : x i < ∑ k ∈ F.N, F.L i k := lt_of_lt_of_le hlt hyle
    rw [hx i hi] at hxlt ⊢
    rcases min_choice (F.z i + ∑ k ∈ F.N, relLiab F k i * x k) (∑ k ∈ F.N, F.L i k) with h | h
    · rw [h]
    · rw [h] at hxlt; exact absurd hxlt (lt_irrefl _)
  have hyS : ∀ i ∈ S, y i ≤ F.z i + ∑ k ∈ F.N, relLiab F k i * y k := by
    intro i hiS
    have hi := hSsub hiS
    rw [hy i hi]; exact min_le_left _ _
  -- difference inequality
  have hdiff : ∀ i ∈ S, y i - x i ≤ ∑ k ∈ S, relLiab F k i * (y k - x k) := by
    intro i hiS
    have h1 : y i - x i ≤ ∑ k ∈ F.N, relLiab F k i * (y k - x k) := by
      have := hyS i hiS
      rw [hxS i hiS] at ⊢
      have e : ∑ k ∈ F.N, relLiab F k i * (y k - x k) =
          ∑ k ∈ F.N, relLiab F k i * y k - ∑ k ∈ F.N, relLiab F k i * x k := by
        rw [← Finset.sum_sub_distrib]; congr 1; ext k; ring
      rw [e]; linarith
    refine h1.trans ?_
    rw [← Finset.sum_filter_add_sum_filter_not F.N (fun k => x k < y k)]
    have h2 : ∑ k ∈ F.N.filter (fun k => ¬ x k < y k), relLiab F k i * (y k - x k) ≤ 0 := by
      apply Finset.sum_nonpos
      intro k hk
      have hk' := (Finset.mem_filter.1 hk).2
      push Not at hk'
      exact mul_nonpos_of_nonneg_of_nonpos (fnp_relLiab_nonneg F k i) (by linarith)
    linarith
  have hsum : ∑ i ∈ S, (y i - x i) ≤ ∑ k ∈ S, (y k - x k) * c k := by
    calc ∑ i ∈ S, (y i - x i) ≤ ∑ i ∈ S, ∑ k ∈ S, relLiab F k i * (y k - x k) :=
          Finset.sum_le_sum hdiff
      _ = ∑ k ∈ S, ∑ i ∈ S, relLiab F k i * (y k - x k) := Finset.sum_comm
      _ = ∑ k ∈ S, (y k - x k) * c k := by
          apply Finset.sum_congr rfl; intro k _
          rw [hc]; simp only; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  have hzero : ∑ k ∈ S, (y k - x k) * (1 - c k) = 0 := by
    apply le_antisymm
    · have e : ∑ k ∈ S, (y k - x k) * (1 - c k) =
          ∑ k ∈ S, (y k - x k) - ∑ k ∈ S, (y k - x k) * c k := by
        rw [← Finset.sum_sub_distrib]; congr 1; ext k; ring
      rw [e]; linarith
    · apply Finset.sum_nonneg; intro k hk
      have := (Finset.mem_filter.1 hk).2
      exact mul_nonneg (by linarith) (by linarith [hc1 k])
  have hcS : ∀ k ∈ S, c k = 1 := by
    intro k hk
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun k hk => by
      have := (Finset.mem_filter.1 hk).2
      exact mul_nonneg (by linarith) (by linarith [hc1 k]))).1 hzero k hk
    have hpos : 0 < y k - x k := by have := (Finset.mem_filter.1 hk).2; linarith
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · linarith
  -- sum x over S
  have hX : ∑ i ∈ S, x i = ∑ i ∈ S, F.z i + ∑ k ∈ F.N, x k * c k := by
    rw [Finset.sum_congr rfl hxS, Finset.sum_add_distrib, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl; intro k _
    rw [hc]; simp only; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  have hX2 : ∑ k ∈ S, x k ≤ ∑ k ∈ F.N, x k * c k := by
    calc ∑ k ∈ S, x k = ∑ k ∈ S, x k * c k := by
          apply Finset.sum_congr rfl; intro k hk; rw [hcS k hk, mul_one]
      _ ≤ ∑ k ∈ F.N, x k * c k :=
          Finset.sum_le_sum_of_subset_of_nonneg hSsub
            (fun k hk _ => mul_nonneg (hx0 k hk) (hc0 k))
  have hzpos : 0 < ∑ i ∈ S, F.z i :=
    Finset.sum_pos (fun i hi => F.z_pos i (hSsub hi)) hSne
  linarith

lemma fnp_unique (F : FinNet) (P Q : ℕ → ℕ → ℝ) (hP : IsPropSolution F P)
    (hQ : IsPropSolution F Q) : P = Q := by
  obtain ⟨hPf, hPx⟩ := fnp_sol_struct F P hP
  obtain ⟨hQf, hQx⟩ := fnp_sol_struct F Q hQ
  have hP0 : ∀ i ∈ F.N, 0 ≤ ∑ l ∈ F.N, P i l := fun i _ =>
    Finset.sum_nonneg fun l _ => hP.1.1 i l
  have hQ0 : ∀ i ∈ F.N, 0 ≤ ∑ l ∈ F.N, Q i l := fun i _ =>
    Finset.sum_nonneg fun l _ => hQ.1.1 i l
  have h1 := fnp_fix_le F (fun i => ∑ l ∈ F.N, P i l) (fun i => ∑ l ∈ F.N, Q i l) hP0 hPx hQx
  have h2 := fnp_fix_le F (fun i => ∑ l ∈ F.N, Q i l) (fun i => ∑ l ∈ F.N, P i l) hQ0 hQx hPx
  funext i j
  by_cases hij : i ∈ F.N ∧ j ∈ F.N
  · rw [hPf i hij.1 j hij.2, hQf i hij.1 j hij.2]
    congr 1
    exact le_antisymm (h2 i hij.1) (h1 i hij.1)
  · have h' : i ∉ F.N ∨ j ∉ F.N := by tauto
    rw [hP.1.2.2 i j h', hQ.1.2.2 i j h']

lemma fnp_exists (F : FinNet) : ∃ P : ℕ → ℕ → ℝ, IsPropSolution F P := by
  classical
  set hi : ℕ → ℝ := fun i => ∑ k ∈ F.N, F.L i k with hhi
  have hfact : Fact ((0 : ℕ → ℝ) ≤ hi) := ⟨fun i => fnp_rowsum_nonneg F i⟩
  let g : (ℕ → ℝ) → ℕ → ℝ := fun x i =>
    if i ∈ F.N then min (F.z i + ∑ k ∈ F.N, relLiab F k i * x k) (hi i) else 0
  have gmem : ∀ x : Set.Icc (0 : ℕ → ℝ) hi, g x.1 ∈ Set.Icc (0 : ℕ → ℝ) hi := by
    intro x
    constructor
    · intro i
      simp only [g, Pi.zero_apply]
      split_ifs
      · apply le_min
        · exact add_nonneg (fnp_z_nonneg F i)
            (Finset.sum_nonneg fun k _ => mul_nonneg (fnp_relLiab_nonneg F k i) (x.2.1 k))
        · exact fnp_rowsum_nonneg F i
      · exact le_rfl
    · intro i
      simp only [g]
      split_ifs
      · exact min_le_right _ _
      · exact fnp_rowsum_nonneg F i
  let T : Set.Icc (0 : ℕ → ℝ) hi →o Set.Icc (0 : ℕ → ℝ) hi :=
    { toFun := fun x => ⟨g x.1, gmem x⟩
      monotone' := by
        intro x y hxy i
        simp only [g]
        split_ifs
        · apply min_le_min_right
          apply add_le_add_right
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_left (hxy k) (fnp_relLiab_nonneg F k i)
        · exact le_rfl }
  set x := (OrderHom.lfp T).1 with hxdef
  have hfix : g x = x := by
    have := OrderHom.map_lfp T
    exact congrArg Subtype.val this
  refine ⟨fun i j => relLiab F i j * x i, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i j
    exact mul_nonneg (fnp_relLiab_nonneg F i j) ((OrderHom.lfp T).2.1 i)
  · intro i
    simp [relLiab, F.L_diag i]
  · intro i j h
    simp [relLiab, F.L_out i j h]
  · intro i hiN j _
    simp only
    rw [fnp_min_eq]
    congr 1
    conv_lhs => rw [← hfix]
    simp only [g, if_pos hiN, hhi]

theorem fnp_eisenberg_noe (F : FinNet) : ∃! P : ℕ → ℕ → ℝ, IsPropSolution F P := by
  obtain ⟨P, hP⟩ := fnp_exists F
  exact ⟨P, hP, fun Q hQ => fnp_unique F Q P hQ hP⟩

end FinNetProp.Mitosis

theorem solution (F : FinNetProp.Mitosis.FinNet) :
    ∃! P : ℕ → ℕ → ℝ, FinNetProp.Mitosis.IsPropSolution F P :=
  FinNetProp.Mitosis.fnp_eisenberg_noe F
