-- Prove2me | solution 1 for FinNetProp.Mitosis.eq_A_1_split_solution
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T16:07:22.318311+00:00
-- url     : https://prove2.me/submissions/a33294de-f63a-4568-9aea-544fd5ad1cca

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

lemma fnp_rowtotal (F : FinNet) (P : ℕ → ℕ → ℝ) (hP : IsPropSolution F P) :
    ∀ i ∈ F.N, ∑ l ∈ F.N, P i l =
      min (F.z i + ∑ k ∈ F.N, P k i) (∑ k ∈ F.N, F.L i k) := by
  obtain ⟨⟨hnn, _, _⟩, heq⟩ := hP
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

theorem fnp_split (F : FinNet) (P : ℕ → ℕ → ℝ) (hP : IsPropSolution F P)
    (j : ℕ) (hj : j ∈ F.N) (K : Finset ℕ) (hK : Disjoint K F.N) (F' : FinNet)
    (hF' : IsSplit F j K F') :
    IsPropSolution F' (splitPay F.N P j K) := by
  classical
  obtain ⟨hN', hzJ, hzE, hLJE, hLEJ, hLJJ, hLEE⟩ := hF'
  set m : ℝ := (K.card : ℝ) + 1 with hm
  have hmpos : 0 < m := by positivity
  set J := insert j K with hJ
  set E := F.N.erase j with hE
  have hjK : j ∉ K := fun h => Finset.disjoint_left.1 hK h hj
  have hJE : ∀ x, x ∈ J → x ∉ E := by
    intro x hx hxE
    rcases Finset.mem_insert.1 hx with h | h
    · exact (Finset.mem_erase.1 hxE).1 h
    · exact Finset.disjoint_left.1 hK h (Finset.mem_erase.1 hxE).2
  have hEJ : ∀ x, x ∈ E → x ∉ J := fun x hx hxJ => hJE x hxJ hx
  have hcardJ : (J.card : ℝ) = m := by
    rw [hJ, Finset.card_insert_of_notMem hjK]; push_cast; ring
  have hNsplit : ∀ f : ℕ → ℝ, ∑ c ∈ F'.N, f c = ∑ c ∈ E, f c + ∑ c ∈ J, f c := by
    intro f
    have hdisj : Disjoint E J := Finset.disjoint_left.2 hEJ
    have hU : F'.N = E ∪ J := by
      rw [hN']; ext x
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, hE, hJ]
      constructor
      · rintro (h | h)
        · by_cases hx : x = j
          · exact Or.inr (Or.inl hx)
          · exact Or.inl ⟨hx, h⟩
        · exact Or.inr (Or.inr h)
      · rintro (⟨_, h⟩ | h | h)
        · exact Or.inl h
        · subst h; exact Or.inl hj
        · exact Or.inr h
    rw [hU, Finset.sum_union hdisj]
  have hsumE : ∀ f : ℕ → ℝ, f j = 0 → ∑ c ∈ E, f c = ∑ c ∈ F.N, f c := by
    intro f hf; exact Finset.sum_erase _ hf
  have hsumE' : ∀ f : ℕ → ℝ, ∑ c ∈ F.N, f c = f j + ∑ c ∈ E, f c := by
    intro f; exact (Finset.add_sum_erase _ _ hj).symm
  -- splitPay evaluations
  have sp1 : ∀ k ∈ J, ∀ c ∈ E, splitPay F.N P j K k c = P j c / m := by
    intro k hk c hc; simp only [splitPay]; rw [if_pos ⟨hk, hc⟩]
  have sp2 : ∀ a ∈ E, ∀ c ∈ J, splitPay F.N P j K a c = P a j / m := by
    intro a ha c hc; simp only [splitPay]
    rw [if_neg (fun h => hEJ a ha h.1), if_pos ⟨ha, hc⟩]
  have sp3 : ∀ a ∈ J, ∀ c ∈ J, splitPay F.N P j K a c = 0 := by
    intro a ha c hc; simp only [splitPay]
    rw [if_neg (fun h => hJE c hc h.2), if_neg (fun h => hJE a ha h.1),
      if_neg (fun h => hJE a ha h.1)]
  have sp4 : ∀ a ∈ E, ∀ c ∈ E, splitPay F.N P j K a c = P a c := by
    intro a ha c hc; simp only [splitPay]
    rw [if_neg (fun h => hEJ a ha h.1), if_neg (fun h => hEJ c hc h.2), if_pos ⟨ha, hc⟩]
  have hPjj : P j j = 0 := hP.1.2.1 j
  have hLjj : F.L j j = 0 := F.L_diag j
  -- row sums of L'
  have hLbarJ : ∀ a ∈ J, ∑ c ∈ F'.N, F'.L a c = (∑ c ∈ F.N, F.L j c) / m := by
    intro a ha
    rw [hNsplit, Finset.sum_congr rfl (fun c hc => hLJE a ha c hc),
      Finset.sum_congr rfl (fun c hc => hLJJ a ha c hc), Finset.sum_const_zero, add_zero,
      ← Finset.sum_div, hsumE (fun c => F.L j c) hLjj]
  have hLbarE : ∀ a ∈ E, ∑ c ∈ F'.N, F'.L a c = ∑ c ∈ F.N, F.L a c := by
    intro a ha
    rw [hNsplit, Finset.sum_congr rfl (fun c hc => hLEE a ha c hc),
      Finset.sum_congr rfl (fun c hc => hLEJ c hc a ha), Finset.sum_const, nsmul_eq_mul,
      hcardJ, hsumE' (fun c => F.L a c)]
    field_simp; ring
  -- asset values
  have hAJ : ∀ a ∈ J, F'.z a + ∑ k ∈ F'.N, splitPay F.N P j K k a =
      (F.z j + ∑ k ∈ F.N, P k j) / m := by
    intro a ha
    rw [hNsplit, Finset.sum_congr rfl (fun k hk => sp2 k hk a ha),
      Finset.sum_congr rfl (fun k hk => sp3 k hk a ha), Finset.sum_const_zero, add_zero,
      hzJ a ha, ← Finset.sum_div, hsumE (fun k => P k j) hPjj, add_div]
  have hAE : ∀ a ∈ E, F'.z a + ∑ k ∈ F'.N, splitPay F.N P j K k a =
      F.z a + ∑ k ∈ F.N, P k a := by
    intro a ha
    rw [hNsplit, Finset.sum_congr rfl (fun k hk => sp4 k hk a ha),
      Finset.sum_congr rfl (fun k hk => sp1 k hk a ha), Finset.sum_const, nsmul_eq_mul,
      hcardJ, hzE a ha, hsumE' (fun k => P k a)]
    field_simp; ring
  -- relLiab values
  have hrelJE : ∀ a ∈ J, ∀ c ∈ E, relLiab F' a c = relLiab F j c := by
    intro a ha c hc
    unfold relLiab
    rw [hLJE a ha c hc, hLbarJ a ha]
    by_cases h0 : F.L j c = 0
    · simp [h0]
    · have : F.L j c / m ≠ 0 := div_ne_zero h0 hmpos.ne'
      rw [if_neg this, if_neg h0]
      field_simp
  have hrelEJ : ∀ a ∈ E, ∀ c ∈ J, relLiab F' a c = relLiab F a j / m := by
    intro a ha c hc
    unfold relLiab
    rw [hLEJ c hc a ha, hLbarE a ha]
    by_cases h0 : F.L a j = 0
    · simp [h0]
    · have : F.L a j / m ≠ 0 := div_ne_zero h0 hmpos.ne'
      rw [if_neg this, if_neg h0]
      field_simp
  have hrelEE : ∀ a ∈ E, ∀ c ∈ E, relLiab F' a c = relLiab F a c := by
    intro a ha c hc
    unfold relLiab
    rw [hLEE a ha c hc, hLbarE a ha]
  have hmemN' : ∀ x ∈ F'.N, x ∈ J ∨ x ∈ E := by
    intro x hx
    rw [hN'] at hx
    rcases Finset.mem_union.1 hx with h | h
    · by_cases hxj : x = j
      · left; rw [hxj]; exact Finset.mem_insert_self _ _
      · right; exact Finset.mem_erase.2 ⟨hxj, h⟩
    · left; exact Finset.mem_insert_of_mem h
  have hJsub : ∀ x ∈ J, x ∈ F'.N := by
    intro x hx; rw [hN']
    rcases Finset.mem_insert.1 hx with h | h
    · rw [h]; exact Finset.mem_union_left _ hj
    · exact Finset.mem_union_right _ h
  have hEsub : ∀ x ∈ E, x ∈ F'.N := by
    intro x hx; rw [hN']; exact Finset.mem_union_left _ (Finset.mem_of_mem_erase hx)
  obtain ⟨⟨hnn, hdiag, hout⟩, heq⟩ := hP
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro a c
    simp only [splitPay]
    split_ifs
    · exact div_nonneg (hnn _ _) hmpos.le
    · exact div_nonneg (hnn _ _) hmpos.le
    · exact hnn _ _
    · exact le_rfl
  · intro a
    simp only [splitPay]
    split_ifs with h1 h2 h3
    · exact absurd h1.2 (hJE a h1.1)
    · exact absurd h2.2 (hEJ a h2.1)
    · exact hdiag a
    · rfl
  · intro a c h
    simp only [splitPay]
    rcases h with h | h
    · rw [if_neg (fun h' => h (hJsub a h'.1)), if_neg (fun h' => h (hEsub a h'.1)),
        if_neg (fun h' => h (hEsub a h'.1))]
    · rw [if_neg (fun h' => h (hEsub c h'.2)), if_neg (fun h' => h (hJsub c h'.2)),
        if_neg (fun h' => h (hEsub c h'.2))]
  · intro a ha c hc
    rw [fnp_min_eq]
    rcases hmemN' a ha with haJ | haE <;> rcases hmemN' c hc with hcJ | hcE
    · rw [sp3 a haJ c hcJ]
      have : relLiab F' a c = 0 := by simp [relLiab, hLJJ a haJ c hcJ]
      rw [this, zero_mul]
    · rw [sp1 a haJ c hcE, hrelJE a haJ c hcE, hAJ a haJ, hLbarJ a haJ,
        heq j hj c (Finset.mem_of_mem_erase hcE), fnp_min_eq, min_div_div_right hmpos.le]
      ring
    · rw [sp2 a haE c hcJ, hrelEJ a haE c hcJ, hAE a haE, hLbarE a haE,
        heq a (Finset.mem_of_mem_erase haE) j hj, fnp_min_eq]
      ring
    · rw [sp4 a haE c hcE, hrelEE a haE c hcE, hAE a haE, hLbarE a haE,
        heq a (Finset.mem_of_mem_erase haE) c (Finset.mem_of_mem_erase hcE), fnp_min_eq]

end FinNetProp.Mitosis

theorem solution (F : FinNetProp.Mitosis.FinNet) (P : ℕ → ℕ → ℝ)
    (hP : FinNetProp.Mitosis.IsPropSolution F P)
    (j : ℕ) (hj : j ∈ F.N) (K : Finset ℕ) (hK : Disjoint K F.N) (F' : FinNetProp.Mitosis.FinNet)
    (hF' : FinNetProp.Mitosis.IsSplit F j K F') :
    FinNetProp.Mitosis.IsPropSolution F' (FinNetProp.Mitosis.splitPay F.N P j K) :=
  FinNetProp.Mitosis.fnp_split F P hP j hj K hK F' hF'
