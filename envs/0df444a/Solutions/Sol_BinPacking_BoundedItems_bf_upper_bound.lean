-- Prove2me | solution 1 for BinPacking.BoundedItems.bf_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T10:30:28.392714+00:00
-- url     : https://prove2.me/submissions/9188e3e0-820a-4289-89f0-85292ac8e164

import Mathlib
import Definitions.Def_BinPacking_BoundedItems_Model

namespace BinPacking.BoundedItems

namespace BFUB0bf1

/-- bin `k` of a packing (empty past the end). -/
noncomputable def G (P : List (List ℝ)) (k : ℕ) : List ℝ := P.getD k []

/-- total contents of a packing. -/
noncomputable def total (P : List (List ℝ)) : ℝ :=
  ∑ k ∈ Finset.range P.length, level (G P k)

lemma level_append (B : List ℝ) (a : ℝ) : level (B ++ [a]) = level B + a := by
  simp [level]

lemma G_set (P : List (List ℝ)) (i k : ℕ) (hi : i < P.length) (x : List ℝ) :
    G (P.set i x) k = if k = i then x else G P k := by
  unfold G
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = k
  · subst h; simp [hi]
  · simp [h, Ne.symm h]

lemma G_append_lt (P : List (List ℝ)) (a : ℝ) (k : ℕ) (hk : k < P.length) :
    G (P ++ [[a]]) k = G P k := by
  unfold G; exact List.getD_append _ _ _ _ hk

lemma G_append_eq (P : List (List ℝ)) (a : ℝ) :
    G (P ++ [[a]]) P.length = [a] := by
  unfold G; rw [List.getD_append_right _ _ _ _ le_rfl]; simp

/-- facts about the Best-Fit choice. -/
lemma bfChoice_some (a : ℝ) (P : List (List ℝ)) (i : ℕ) (h : bfChoice a P = some i) :
    i < P.length ∧ level (G P i) + a ≤ 1 ∧
      ∀ j < P.length, level (G P j) + a ≤ 1 → level (G P j) ≤ level (G P i) := by
  unfold bfChoice at h
  simp only at h
  have hmem := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hmem
  refine ⟨hmem.1, hmem.2, ?_⟩
  intro j hj hfit
  simp only [List.all_eq_true, List.mem_filter, List.mem_range, decide_eq_true_eq] at hp
  exact hp j ⟨hj, hfit⟩

lemma bfChoice_none (a : ℝ) (P : List (List ℝ)) (h : bfChoice a P = none) :
    ∀ j < P.length, 1 < level (G P j) + a := by
  intro j hj
  by_contra hcon
  push Not at hcon
  unfold bfChoice at h
  simp only at h
  set fits := (List.range P.length).filter (fun i => decide (level (P.getD i []) + a ≤ 1))
    with hfits
  have hjm : j ∈ fits := by
    simp only [hfits, List.mem_filter, List.mem_range, decide_eq_true_eq]; exact ⟨hj, hcon⟩
  obtain ⟨k, hk, hkmax⟩ := fits.toFinset.exists_max_image (fun i => level (P.getD i []))
    ⟨j, List.mem_toFinset.mpr hjm⟩
  rw [List.find?_eq_none] at h
  have := h k (List.mem_toFinset.mp hk)
  apply this
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro x hx
  exact hkmax x (List.mem_toFinset.mpr hx)

lemma total_bfInsert (a : ℝ) (P : List (List ℝ)) :
    total (bfInsert a P) = total P + a := by
  unfold bfInsert
  rcases hc : bfChoice a P with _ | i
  · simp only
    unfold total
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ, G_append_eq]
    rw [Finset.sum_congr rfl (fun k hk => by rw [G_append_lt P a k (Finset.mem_range.mp hk)])]
    simp [level]
  · simp only
    obtain ⟨hi, -, -⟩ := bfChoice_some a P i hc
    unfold total
    rw [List.length_set]
    have : ∀ k ∈ Finset.range P.length, level (G (P.set i (P.getD i [] ++ [a])) k)
        = level (G P k) + if k = i then a else 0 := by
      intro k _
      rw [G_set P i k hi]
      split_ifs with hk
      · subst hk; rw [level_append]; rfl
      · simp
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [Finset.mem_range.mpr hi]

/-- the invariant. -/
structure Inv (α θ : ℝ) (P : List (List ℝ)) : Prop where
  items : ∀ k, ∀ c ∈ G P k, 0 < c ∧ c ≤ α
  nonlast : ∀ k, k + 1 < P.length → 1 - α < level (G P k)
  pair : ∀ i j, i < j → j < P.length → level (G P i) < θ → level (G P j) < θ →
    ∀ c ∈ G P j, 1 - level (G P i) < c

lemma level_nonneg (α : ℝ) (B : List ℝ) (h : ∀ c ∈ B, 0 < c ∧ c ≤ α) : 0 ≤ level B := by
  unfold level
  exact List.sum_nonneg (fun c hc => (h c hc).1.le)

/-- counting lemma: a bin whose items are all `> 1/(m+1)` and `≤ α`, with level `< m/(m+1)`,
has level `≤ 1 - α`. -/
lemma count_lemma (α δ : ℝ) (hα0 : 0 ≤ α) (m : ℕ) (hm1 : 1 ≤ m) (hmα : (m : ℝ) * α ≤ 1)
    (hδ : 1 / ((m : ℝ) + 1) < δ) (B : List ℝ) (hB : ∀ c ∈ B, δ < c ∧ c ≤ α)
    (hlev : level B < (m : ℝ) / ((m : ℝ) + 1)) : level B ≤ 1 - α := by
  unfold level at *
  have h1 : (B.length : ℝ) * δ ≤ B.sum := by
    have := List.card_nsmul_le_sum B δ (fun c hc => (hB c hc).1.le)
    simpa [nsmul_eq_mul] using this
  have h2 : B.sum ≤ (B.length : ℝ) * α := by
    have := List.sum_le_card_nsmul B α (fun c hc => (hB c hc).2)
    simpa [nsmul_eq_mul] using this
  have hmpos : (0 : ℝ) < m + 1 := by positivity
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  rcases Nat.lt_or_ge B.length m with hn | hn
  · have hn' : (B.length : ℝ) ≤ m - 1 := by
      have : B.length + 1 ≤ m := hn
      have : ((B.length : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast this
      linarith
    have hlen0 : (0 : ℝ) ≤ B.length := by positivity
    nlinarith
  · exfalso
    have hn' : (m : ℝ) ≤ B.length := by exact_mod_cast hn
    have hδpos : 0 < δ := lt_trans (by positivity) hδ
    have h3 : (m : ℝ) * δ ≤ B.sum := le_trans (by nlinarith) h1
    have h4 : (m : ℝ) / ((m : ℝ) + 1) < (m : ℝ) * δ := by
      rw [div_lt_iff₀ hmpos]
      have := (div_lt_iff₀ hmpos).mp hδ
      nlinarith
    linarith

lemma Inv_nil (α θ : ℝ) : Inv α θ [] := by
  refine ⟨?_, ?_, ?_⟩
  · intro k c hc; simp [G] at hc
  · intro k hk; simp at hk
  · intro i j _ hj; simp at hj

lemma Inv_bfInsert (α : ℝ) (m : ℕ) (hm1 : 1 ≤ m) (hmα : (m : ℝ) * α ≤ 1)
    (P : List (List ℝ)) (hP : Inv α ((m : ℝ) / ((m : ℝ) + 1)) P)
    (a : ℝ) (ha : 0 < a) (haα : a ≤ α) :
    Inv α ((m : ℝ) / ((m : ℝ) + 1)) (bfInsert a P) := by
  have hα0 : 0 ≤ α := by linarith
  set θ := (m : ℝ) / ((m : ℝ) + 1) with hθ
  have hmpos : (0 : ℝ) < m + 1 := by positivity
  have h1θ : 1 - θ = 1 / ((m : ℝ) + 1) := by
    rw [hθ]; field_simp; ring
  unfold bfInsert
  rcases hc : bfChoice a P with _ | i0
  · -- new bin
    simp only
    have hnone := bfChoice_none a P hc
    have hG : ∀ k, G (P ++ [[a]]) k = if k < P.length then G P k else
        if k = P.length then [a] else [] := by
      intro k
      split_ifs with h1 h2
      · exact G_append_lt P a k h1
      · subst h2; exact G_append_eq P a
      · unfold G; apply List.getD_eq_default; simp; omega
    refine ⟨?_, ?_, ?_⟩
    · intro k c hcm
      rw [hG k] at hcm
      split_ifs at hcm with h1 h2
      · exact hP.items k c hcm
      · simp at hcm; subst hcm; exact ⟨ha, haα⟩
      · simp at hcm
    · intro k hk
      simp only [List.length_append, List.length_singleton] at hk
      rw [hG k, if_pos (by omega)]
      by_cases hk' : k + 1 < P.length
      · exact hP.nonlast k hk'
      · have := hnone k (by omega)
        linarith
    · intro i j hij hj hi hjθ c hcm
      simp only [List.length_append, List.length_singleton] at hj
      rw [hG i, if_pos (by omega)] at hi ⊢
      rw [hG j] at hjθ hcm
      by_cases hj' : j < P.length
      · rw [if_pos hj'] at hjθ hcm
        exact hP.pair i j hij hj' hi hjθ c hcm
      · rw [if_neg hj', if_pos (by omega)] at hcm
        simp at hcm; subst hcm
        have := hnone i (by omega)
        linarith
  · -- placed into bin i0
    simp only
    obtain ⟨hi0, hfit0, hmax⟩ := bfChoice_some a P i0 hc
    have hG : ∀ k, G (P.set i0 (P.getD i0 [] ++ [a])) k =
        if k = i0 then G P i0 ++ [a] else G P k := fun k => G_set P i0 k hi0 _
    refine ⟨?_, ?_, ?_⟩
    · intro k c hcm
      rw [hG k] at hcm
      split_ifs at hcm with h1
      · rcases List.mem_append.mp hcm with h | h
        · exact hP.items i0 c h
        · simp at h; subst h; exact ⟨ha, haα⟩
      · exact hP.items k c hcm
    · intro k hk
      rw [List.length_set] at hk
      rw [hG k]
      split_ifs with h1
      · subst h1; rw [level_append]; have := hP.nonlast k hk; linarith
      · exact hP.nonlast k hk
    · intro i j hij hj hi hjθ c hcm
      rw [List.length_set] at hj
      rw [hG i] at hi ⊢
      rw [hG j] at hjθ hcm
      by_cases hji : j = i0
      · -- the item went into the higher bin j
        have hine : i ≠ i0 := by omega
        rw [if_neg hine] at hi ⊢
        rw [if_pos hji, ← hji] at hjθ hcm
        rw [level_append] at hjθ
        have hjθ' : level (G P j) < θ := by linarith
        rcases List.mem_append.mp hcm with h | h
        · exact hP.pair i j hij hj hi hjθ' c h
        · simp at h; subst h
          by_contra hcon
          push Not at hcon
          have hle := hmax i (by omega) (by linarith)
          rw [← hji] at hle
          -- bin j's items all exceed 1 - level i > 1/(m+1)
          have hδ : 1 / ((m : ℝ) + 1) < 1 - level (G P i) := by linarith
          have hcnt := count_lemma α (1 - level (G P i)) hα0 m hm1 hmα hδ (G P j)
            (fun c hc => ⟨hP.pair i j hij hj hi hjθ' c hc, (hP.items j c hc).2⟩) hjθ'
          have hnl := hP.nonlast i (by omega)
          linarith
      · rw [if_neg hji] at hjθ hcm
        by_cases hii : i = i0
        · rw [if_pos hii] at hi ⊢
          rw [level_append] at hi ⊢
          have hi' : level (G P i0) < θ := by linarith
          subst hii
          have := hP.pair i j hij hj hi' hjθ c hcm
          linarith
        · rw [if_neg hii] at hi ⊢
          exact hP.pair i j hij hj hi hjθ c hcm

lemma foldl_facts (α : ℝ) (m : ℕ) (hm1 : 1 ≤ m) (hmα : (m : ℝ) * α ≤ 1) :
    ∀ (L : List ℝ) (P : List (List ℝ)), Inv α ((m : ℝ) / ((m : ℝ) + 1)) P →
      (∀ a ∈ L, 0 < a ∧ a ≤ α) →
      Inv α ((m : ℝ) / ((m : ℝ) + 1)) (L.foldl (fun P a => bfInsert a P) P) ∧
      total (L.foldl (fun P a => bfInsert a P) P) = total P + L.sum := by
  intro L
  induction L with
  | nil => intro P hP _; simp [hP]
  | cons a L ih =>
    intro P hP hL
    simp only [List.foldl_cons, List.sum_cons]
    have ha := hL a (by simp)
    obtain ⟨h1, h2⟩ := ih (bfInsert a P) (Inv_bfInsert α m hm1 hmα P hP a ha.1 ha.2)
      (fun b hb => hL b (by simp [hb]))
    refine ⟨h1, ?_⟩
    rw [h2, total_bfInsert]; ring

lemma sum_le_optBins (L : List ℝ) (hL : IsList L) : L.sum ≤ (optBins L : ℝ) := by
  have hne : {b : ℕ | ∃ f : Fin L.length → Fin b, IsPacking L b f}.Nonempty := by
    refine ⟨L.length, fun i => i, ?_⟩
    intro j
    have : Finset.univ.filter (fun i : Fin L.length => i = j) = {j} := by
      ext x; simp
    rw [this, Finset.sum_singleton]
    exact (hL _ (List.get_mem L j)).2
  obtain ⟨f, hf⟩ := Nat.sInf_mem hne
  have hsum : L.sum = ∑ i : Fin L.length, L.get i := by
    rw [← List.sum_ofFn, List.ofFn_get]
  have key : ∑ i : Fin L.length, L.get i ≤
      ((sInf {b : ℕ | ∃ f : Fin L.length → Fin b, IsPacking L b f} : ℕ) : ℝ) := by
    rw [← Finset.sum_fiberwise Finset.univ f (fun i => L.get i)]
    calc _ ≤ ∑ _j : Fin (sInf {b : ℕ | ∃ f : Fin L.length → Fin b, IsPacking L b f}), (1 : ℝ) :=
          Finset.sum_le_sum (fun j _ => hf j)
      _ = _ := by simp
  rw [hsum]
  exact key

end BFUB0bf1

end BinPacking.BoundedItems

open BinPacking.BoundedItems.BFUB0bf1 in
open BinPacking.BoundedItems in
theorem solution (α : ℝ) (hα : 0 < α) (hα2 : α ≤ 1 / 2) (m : ℕ) (hm : m = ⌊α⁻¹⌋₊)
    (L : List ℝ) (hL : IsList L) (hLα : ∀ a ∈ L, a ≤ α) :
    (BF L : ℝ) ≤ ((m : ℝ) + 1) / m * (optBins L : ℝ) + 2 := by
  have hinv : (2 : ℝ) ≤ α⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hα]; linarith
  have hm2 : 2 ≤ m := by
    rw [hm]; exact Nat.le_floor (by exact_mod_cast hinv)
  have hm1 : 1 ≤ m := by omega
  have hmα : (m : ℝ) * α ≤ 1 := by
    have : (m : ℝ) ≤ α⁻¹ := by rw [hm]; exact Nat.floor_le (by positivity)
    calc (m : ℝ) * α ≤ α⁻¹ * α := by gcongr
      _ = 1 := inv_mul_cancel₀ hα.ne'
  set θ := (m : ℝ) / ((m : ℝ) + 1) with hθ
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hθpos : 0 < θ := by positivity
  have hα0 : 0 ≤ α := hα.le
  obtain ⟨hI, hT⟩ := foldl_facts α m hm1 hmα L [] (Inv_nil α θ)
    (fun a ha => ⟨(hL a ha).1, hLα a ha⟩)
  have hBF : BF L = (bfPack L).length := rfl
  have hpack : bfPack L = L.foldl (fun P a => bfInsert a P) [] := rfl
  rw [← hpack] at hI hT
  set P := bfPack L with hP
  set N := P.length with hN
  have htot : total P = L.sum := by rw [hT]; simp [total]
  -- at most one low non-last bin
  have hlow : ∀ i j, i < j → j + 1 < N → level (G P i) < θ → level (G P j) < θ → False := by
    intro i j hij hj hi hjθ
    have hδ : 1 / ((m : ℝ) + 1) < 1 - level (G P i) := by
      have : 1 - θ = 1 / ((m : ℝ) + 1) := by rw [hθ]; field_simp; ring
      linarith
    have hcnt := count_lemma α (1 - level (G P i)) hα0 m hm1 hmα hδ (G P j)
      (fun c hc => ⟨hI.pair i j hij (by omega) hi hjθ c hc, (hI.items j c hc).2⟩) hjθ
    have := hI.nonlast j hj
    linarith
  have hex : ∃ i0, ∀ k, k + 1 < N → k ≠ i0 → θ ≤ level (G P k) := by
    by_cases h : ∃ i0, i0 + 1 < N ∧ level (G P i0) < θ
    · obtain ⟨i0, hi0, hl⟩ := h
      refine ⟨i0, fun k hk hne => ?_⟩
      by_contra hc
      push Not at hc
      rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · exact hlow k i0 h' hi0 hc hl
      · exact hlow i0 k h' hk hl hc
    · push Not at h
      exact ⟨0, fun k hk _ => h k hk⟩
  obtain ⟨i0, hi0⟩ := hex
  have hnn : ∀ k, 0 ≤ level (G P k) := fun k => level_nonneg α _ (hI.items k)
  have hsumge : (((N - 1) - 1 : ℕ) : ℝ) * θ ≤ total P := by
    unfold total
    calc (((N - 1) - 1 : ℕ) : ℝ) * θ ≤ (((Finset.range (N - 1)).erase i0).card : ℝ) * θ := by
          gcongr
          have := Finset.pred_card_le_card_erase (s := Finset.range (N - 1)) (a := i0)
          simp only [Finset.card_range] at this
          exact this
      _ = ∑ _k ∈ (Finset.range (N - 1)).erase i0, θ := by simp
      _ ≤ ∑ k ∈ (Finset.range (N - 1)).erase i0, level (G P k) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Finset.mem_erase, Finset.mem_range] at hk
          exact hi0 k (by omega) hk.1
      _ ≤ ∑ k ∈ Finset.range (N - 1), level (G P k) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun k _ _ => hnn k)
      _ ≤ ∑ k ∈ Finset.range N, level (G P k) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (Nat.sub_le N 1)) (fun k _ _ => hnn k)
  have hcast : (N : ℝ) - 2 ≤ (((N - 1) - 1 : ℕ) : ℝ) := by
    rcases Nat.lt_or_ge N 2 with h | h
    · have : (N : ℝ) < 2 := by exact_mod_cast h
      have : (0 : ℝ) ≤ (((N - 1) - 1 : ℕ) : ℝ) := by positivity
      linarith
    · rw [show N - 1 - 1 = N - 2 by omega, Nat.cast_sub h]; simp
  have hopt := sum_le_optBins L hL
  rw [htot] at hsumge
  rw [hBF]
  have hfin : ((N : ℝ) - 2) * θ ≤ optBins L := by
    have : ((N : ℝ) - 2) * θ ≤ (((N - 1) - 1 : ℕ) : ℝ) * θ := by gcongr
    linarith
  rw [hθ] at hfin
  have hfin' : ((N : ℝ) - 2) * m ≤ (optBins L : ℝ) * ((m : ℝ) + 1) := by
    have h := hfin
    rw [mul_div_assoc', div_le_iff₀ (by positivity)] at h
    linarith
  have : ((N : ℝ) - 2) ≤ ((m : ℝ) + 1) / m * (optBins L : ℝ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hmpos]
    linarith
  show (N : ℝ) ≤ _
  linarith
