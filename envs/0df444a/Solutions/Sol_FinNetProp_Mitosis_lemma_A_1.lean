-- Prove2me | solution 1 for FinNetProp.Mitosis.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T16:12:05.207509+00:00
-- url     : https://prove2.me/submissions/7065ea70-5c52-46c4-bfad-b814350004e9

import Mathlib
import Definitions.Def_FinNetProp_Mitosis_Setting

namespace FinNetProp.Mitosis

open Finset

lemma fnpA_fresh (F : FinNet) (n : ℕ) : ∃ K : Finset ℕ, Disjoint K F.N ∧ K.card = n := by
  refine ⟨Finset.Ico (F.N.sup id + 1) (F.N.sup id + 1 + n), ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hx hxN
    have h1 := (Finset.mem_Ico.1 hx).1
    have h2 : x ≤ F.N.sup id := Finset.le_sup (f := id) hxN
    omega
  · simp

lemma fnpA_split_exists (F : FinNet) (j : ℕ) (hj : j ∈ F.N) (K : Finset ℕ)
    (hK : Disjoint K F.N) : ∃ F' : FinNet, IsSplit F j K F' := by
  classical
  set m : ℝ := (K.card : ℝ) + 1 with hm
  have hmpos : 0 < m := by positivity
  set J := insert j K with hJ
  set E := F.N.erase j with hE
  have hJE : ∀ x, x ∈ J → x ∉ E := by
    intro x hx hxE
    rcases Finset.mem_insert.1 hx with h | h
    · exact (Finset.mem_erase.1 hxE).1 h
    · exact Finset.disjoint_left.1 hK h (Finset.mem_erase.1 hxE).2
  have hmem : ∀ x, x ∈ F.N ∪ K ↔ x ∈ J ∨ x ∈ E := by
    intro x
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, hE, hJ]
    constructor
    · rintro (h | h)
      · by_cases hx : x = j
        · exact Or.inl (Or.inl hx)
        · exact Or.inr ⟨hx, h⟩
      · exact Or.inl (Or.inr h)
    · rintro ((h | h) | ⟨_, h⟩)
      · subst h; exact Or.inl hj
      · exact Or.inr h
      · exact Or.inl h
  let zz : ℕ → ℝ := fun a => if a ∈ J then F.z j / m else if a ∈ E then F.z a else 0
  let LL : ℕ → ℕ → ℝ := fun a c =>
    if a ∈ J ∧ c ∈ E then F.L j c / m
    else if a ∈ E ∧ c ∈ J then F.L a j / m
    else if a ∈ E ∧ c ∈ E then F.L a c
    else 0
  refine ⟨FinNet.mk (F.N ∪ K) ⟨j, Finset.mem_union_left _ hj⟩ zz LL ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro a ha
    simp only [zz]
    rcases (hmem a).1 ha with h | h
    · rw [if_pos h]; exact div_pos (F.z_pos j hj) hmpos
    · rw [if_neg (fun h' => hJE a h' h), if_pos h]
      exact F.z_pos a (Finset.mem_of_mem_erase h)
  · intro a c
    simp only [LL]
    split_ifs
    · exact div_nonneg (F.L_nonneg _ _) hmpos.le
    · exact div_nonneg (F.L_nonneg _ _) hmpos.le
    · exact F.L_nonneg _ _
    · exact le_rfl
  · intro a
    simp only [LL]
    split_ifs with h1 h2 h3
    · exact absurd h1.2 (hJE a h1.1)
    · exact absurd h2.2 (fun h => hJE a h h2.1)
    · exact F.L_diag a
    · rfl
  · intro a ha
    simp only [zz]
    rw [if_neg (fun h => ha ((hmem a).2 (Or.inl h))),
      if_neg (fun h => ha ((hmem a).2 (Or.inr h)))]
  · intro a c h
    simp only [LL]
    rcases h with h | h
    · rw [if_neg (fun h' => h ((hmem a).2 (Or.inl h'.1))),
        if_neg (fun h' => h ((hmem a).2 (Or.inr h'.1))),
        if_neg (fun h' => h ((hmem a).2 (Or.inr h'.1)))]
    · rw [if_neg (fun h' => h ((hmem c).2 (Or.inr h'.2))),
        if_neg (fun h' => h ((hmem c).2 (Or.inl h'.2))),
        if_neg (fun h' => h ((hmem c).2 (Or.inr h'.2)))]
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk; simp only [zz]; rw [if_pos hk]
    · intro i hi; simp only [zz]; rw [if_neg (fun h => hJE i h hi), if_pos hi]
    · intro k hk i hi; simp only [LL]; rw [if_pos ⟨hk, hi⟩]
    · intro k hk i hi; simp only [LL]
      rw [if_neg (fun h => hJE i h.1 hi), if_pos ⟨hi, hk⟩]
    · intro k hk l hl; simp only [LL]
      rw [if_neg (fun h => hJE l hl h.2), if_neg (fun h => hJE k hk h.1),
        if_neg (fun h => hJE k hk h.1)]
    · intro h hh i hi; simp only [LL]
      rw [if_neg (fun h' => hJE h h'.1 hh), if_neg (fun h' => hJE i h'.2 hi), if_pos ⟨hh, hi⟩]

lemma fnpA_zero (b : BankruptcyRule) (himp : Impartial b) (F : FinNet) (i a : ℕ)
    (hi : i ∈ F.N) (ha : a ∈ F.N) (h : F.L i a = 0) : b F i a = 0 := by
  have := himp F i hi a ha i hi (by rw [h, F.L_diag])
  rw [this]; exact (b.mem F).2.1 i

/-- Split agent `k` into `n + 1` identical agents and read off the consequences. -/
lemma fnpA_split_row (b : BankruptcyRule) (himp : Impartial b) (hmit : InvariantToMitosis b)
    (F : FinNet) (i k : ℕ) (hi : i ∈ F.N) (hk : k ∈ F.N) (hik : i ≠ k) (n : ℕ) :
    ∃ F' : FinNet, F.N ⊆ F'.N ∧
      (∀ j ∈ F.N, j ≠ k → F'.L i j = F.L i j ∧ b F' i j = b F i j) ∧
      F'.L i k = F.L i k / ((n : ℝ) + 1) ∧
      b F i k = ((n : ℝ) + 1) * b F' i k := by
  classical
  obtain ⟨K, hK, hcard⟩ := fnpA_fresh F n
  obtain ⟨F', hF'⟩ := fnpA_split_exists F k hk K hK
  have hF'2 := hF'
  obtain ⟨hN', hzJ, hzE, hLJE, hLEJ, hLJJ, hLEE⟩ := hF'2
  obtain ⟨hm1, hm2, hm3⟩ := hmit F k hk K hK F' hF'
  have hiE : i ∈ F.N.erase k := Finset.mem_erase.2 ⟨hik, hi⟩
  have hsub : F.N ⊆ F'.N := by rw [hN']; exact Finset.subset_union_left
  have hkK : k ∉ K := fun h => Finset.disjoint_left.1 hK h hk
  have hJsub : ∀ l ∈ insert k K, l ∈ F'.N := by
    intro l hl; rw [hN']
    rcases Finset.mem_insert.1 hl with h | h
    · rw [h]; exact Finset.mem_union_left _ hk
    · exact Finset.mem_union_right _ h
  refine ⟨F', hsub, ?_, ?_, ?_⟩
  · intro j hj hjk
    have hjE : j ∈ F.N.erase k := Finset.mem_erase.2 ⟨hjk, hj⟩
    exact ⟨hLEE i hiE j hjE, hm3 i hiE j hjE⟩
  · rw [hLEJ k (Finset.mem_insert_self _ _) i hiE, hcard]
  · have heach : ∀ l ∈ insert k K, b F' i l = b F' i k := by
      intro l hl
      apply himp F' i (hsub hi) l (hJsub l hl) k (hJsub k (Finset.mem_insert_self _ _))
      rw [hLEJ l hl i hiE, hLEJ k (Finset.mem_insert_self _ _) i hiE]
    rw [← hm2 i hiE, Finset.sum_congr rfl heach, Finset.sum_const, nsmul_eq_mul,
      Finset.card_insert_of_notMem hkK, hcard]
    push_cast; ring

/-- Step 1 of the proof of Lemma A.1 (`r = 1`). -/
lemma fnpA_step1 (b : BankruptcyRule) (himp : Impartial b) (hmit : InvariantToMitosis b)
    (F : FinNet) (i j k : ℕ) (hi : i ∈ F.N) (hj : j ∈ F.N) (hk : k ∈ F.N) (q : ℕ)
    (hq : 0 < q) (hL : F.L i j = (q : ℝ) * F.L i k) :
    b F i j = (q : ℝ) * b F i k := by
  by_cases h0 : F.L i k = 0
  · rw [fnpA_zero b himp F i j hi hj (by rw [hL, h0, mul_zero]),
      fnpA_zero b himp F i k hi hk h0, mul_zero]
  have hik : i ≠ k := by rintro rfl; exact h0 (F.L_diag i)
  have hij : i ≠ j := by
    rintro rfl
    have : (q : ℝ) * F.L i k = 0 := by rw [← hL, F.L_diag]
    rcases mul_eq_zero.1 this with h | h
    · have : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      exact this h
    · exact h0 h
  -- split j into q agents
  obtain ⟨F', hsub, hrow, hLj, hbj⟩ := fnpA_split_row b himp hmit F i j hi hj hij (q - 1)
  have hq1 : ((q - 1 : ℕ) : ℝ) + 1 = q := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hq1] at hLj hbj
  by_cases hjk : j = k
  · subst hjk
    have hq' : (q : ℝ) = 1 := by
      have := hL
      have h2 : ((q : ℝ) - 1) * F.L i j = 0 := by linarith
      rcases mul_eq_zero.1 h2 with h | h
      · linarith
      · exact absurd h h0
    rw [hq', one_mul]
  obtain ⟨hLk, hbk⟩ := hrow k hk (Ne.symm hjk)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have himp' := himp F' i (hsub hi) j (hsub hj) k (hsub hk)
    (by rw [hLj, hLk, hL]; field_simp)
  rw [hbj, himp', hbk]

theorem fnp_lemma_A_1 (b : BankruptcyRule) (himp : Impartial b) (hmit : InvariantToMitosis b)
    (F : FinNet) (i j k : ℕ) (hi : i ∈ F.N) (hj : j ∈ F.N) (hk : k ∈ F.N) (q r : ℕ)
    (hq : 0 < q) (hr : 0 < r) (hL : F.L i j = ((q : ℝ) / (r : ℝ)) * F.L i k) :
    b F i j = ((q : ℝ) / (r : ℝ)) * b F i k := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  by_cases h0 : F.L i k = 0
  · rw [fnpA_zero b himp F i j hi hj (by rw [hL, h0, mul_zero]),
      fnpA_zero b himp F i k hi hk h0, mul_zero]
  have hik : i ≠ k := by rintro rfl; exact h0 (F.L_diag i)
  by_cases hjk : j = k
  · subst hjk
    have hq' : (q : ℝ) / r = 1 := by
      have h2 : ((q : ℝ) / r - 1) * F.L i j = 0 := by linarith
      rcases mul_eq_zero.1 h2 with h | h
      · linarith
      · exact absurd h h0
    rw [hq', one_mul]
  -- split k into r agents
  obtain ⟨F', hsub, hrow, hLk, hbk⟩ := fnpA_split_row b himp hmit F i k hi hk hik (r - 1)
  have hr1 : ((r - 1 : ℕ) : ℝ) + 1 = r := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hr1] at hLk hbk
  obtain ⟨hLj, hbj⟩ := hrow j hj hjk
  have hstep := fnpA_step1 b himp hmit F' i j k (hsub hi) (hsub hj) (hsub hk) q hq
    (by rw [hLj, hLk, hL]; field_simp)
  rw [← hbj, hstep, hbk]
  field_simp

end FinNetProp.Mitosis

theorem solution (b : FinNetProp.Mitosis.BankruptcyRule) (himp : FinNetProp.Mitosis.Impartial b)
    (hmit : FinNetProp.Mitosis.InvariantToMitosis b)
    (F : FinNetProp.Mitosis.FinNet) (i j k : ℕ) (hi : i ∈ F.N) (hj : j ∈ F.N) (hk : k ∈ F.N)
    (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (hL : F.L i j = ((q : ℝ) / (r : ℝ)) * F.L i k) :
    b F i j = ((q : ℝ) / (r : ℝ)) * b F i k :=
  FinNetProp.Mitosis.fnp_lemma_A_1 b himp hmit F i j k hi hj hk q r hq hr hL
