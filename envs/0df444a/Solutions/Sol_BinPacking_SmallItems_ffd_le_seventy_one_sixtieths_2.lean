-- Prove2me | solution 2 for BinPacking.SmallItems.ffd_le_seventy_one_sixtieths
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T11:32:36.101697+00:00
-- url     : https://prove2.me/submissions/ee741e7b-d57f-4318-a912-64abe6c05f69

import Mathlib
import Definitions.Def_BinPacking_SmallItems_Model
import Definitions.Def_BinPacking_SmallItems_Weight

set_option autoImplicit false


namespace FFBAux_ffb69a58
open BinPacking.SmallItems

open Classical in
noncomputable def gw (b x : ℝ) : ℝ := if ∃ k : ℕ, IsPiece k x ∧ IsPiece k b then w1 x else 0

noncomputable def hw (b : ℝ) (B : List ℝ) : ℝ := (B.map (gw b)).sum

lemma w1_nonneg (x : ℝ) : 0 ≤ w1 x := by unfold w1; positivity

lemma gw_nonneg (b x : ℝ) : 0 ≤ gw b x := by
  unfold gw; split_ifs
  · exact w1_nonneg x
  · exact le_refl 0

lemma hw_append (b : ℝ) (B : List ℝ) (y : ℝ) : hw b (B ++ [y]) = hw b B + gw b y := by
  simp [hw]

lemma piece_pos {k : ℕ} {x : ℝ} (h : IsPiece k x) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨h1, h2⟩ := h
    simp at h1 h2
    linarith
  · exact hk

lemma floor_eq_of_piece {k : ℕ} {x : ℝ} (h : IsPiece k x) : ⌊1 / x⌋₊ = k := by
  have hk := piece_pos h
  obtain ⟨h1, h2⟩ := h
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hx : 0 < x := lt_trans (by positivity) h1
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rw [le_div_iff₀ hx]
    have := (le_div_iff₀ hk').mp h2
    nlinarith
  · rw [div_lt_iff₀ hx]
    have := (div_lt_iff₀ (by positivity : (0:ℝ) < k+1)).mp h1
    nlinarith

lemma piece_of_floor {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : IsPiece ⌊1 / x⌋₊ x := by
  have h1x : (1:ℝ) ≤ 1 / x := by rw [le_div_iff₀ hx]; linarith
  have hk1 : 1 ≤ ⌊1 / x⌋₊ := Nat.le_floor (by simpa using h1x)
  have hk' : (0:ℝ) < (⌊1 / x⌋₊ : ℝ) := by exact_mod_cast hk1
  have hfl : ((⌊1 / x⌋₊ : ℕ) : ℝ) ≤ 1 / x := Nat.floor_le (by positivity)
  have hlt : 1 / x < ((⌊1 / x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  constructor
  · rw [div_lt_iff₀ (by positivity)]
    have := (div_lt_iff₀ hx).mp hlt
    nlinarith
  · rw [le_div_iff₀ hk']
    have := (le_div_iff₀ hx).mp hfl
    nlinarith

lemma foldr_max_eq (a : ℝ) (ha : 0 ≤ a) (B : List ℝ) :
    B.foldr max a = max (B.foldr max 0) a := by
  induction B with
  | nil => simp [ha]
  | cons b B ih => simp only [List.foldr_cons, ih, max_assoc]

lemma le_binMax {x : ℝ} {B : List ℝ} (h : x ∈ B) : x ≤ binMax B := by
  induction B with
  | nil => simp at h
  | cons b B ih =>
    simp only [binMax, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma binMax_mem {B : List ℝ} (hne : B ≠ []) (hpos : ∀ x ∈ B, 0 ≤ x) : binMax B ∈ B := by
  induction B with
  | nil => exact absurd rfl hne
  | cons b B ih =>
    simp only [binMax, List.foldr_cons] at ih ⊢
    by_cases hB : B = []
    · subst hB
      simp [max_eq_left (hpos b (by simp))]
    · rcases max_choice b (B.foldr max 0) with h | h
      · rw [h]; simp
      · rw [h]
        exact List.mem_cons_of_mem _ (ih hB (fun x hx => hpos x (List.mem_cons_of_mem _ hx)))

lemma binMax_append {B : List ℝ} {y : ℝ} (hy : 0 ≤ y) (hle : y ≤ binMax B) :
    binMax (B ++ [y]) = binMax B := by
  unfold binMax
  rw [List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_max_eq _ (le_max_right _ _)]
  unfold binMax at hle
  rw [max_eq_left hy, max_eq_left hle]

lemma binMax_single {y : ℝ} (hy : 0 ≤ y) : binMax [y] = y := by simp [binMax, hy]

lemma getD_lt {α : Type} (P : List α) (j : ℕ) (d : α) (hj : j < P.length) : P.getD j d = P[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl

lemma getD_ge {α : Type} (P : List α) (j : ℕ) (d : α) (hj : P.length ≤ j) : P.getD j d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]; rfl

lemma placeAt_lt {P : List (List ℝ)} {c : ℕ} {y : ℝ} (hc : c < P.length) :
    (placeAt P c y).length = P.length ∧
    ∀ j, (placeAt P c y).getD j [] = if j = c then P.getD j [] ++ [y] else P.getD j [] := by
  refine ⟨by simp [placeAt, hc], fun j => ?_⟩
  simp only [placeAt, hc, if_true]
  rcases lt_or_ge j P.length with hj | hj
  · rw [getD_lt _ _ _ (by simpa using hj), getD_lt _ _ _ hj, List.getElem_mapIdx]
  · rw [getD_ge _ _ _ (by simpa using hj), getD_ge _ _ _ hj]
    have : j ≠ c := by omega
    simp [this]

lemma placeAt_eq {P : List (List ℝ)} {y : ℝ} :
    placeAt P P.length y = P ++ [[y]] := by simp [placeAt]

lemma getD_app_lt (P : List (List ℝ)) (y : ℝ) (j : ℕ) (hj : j < P.length) :
    (P ++ [[y]]).getD j [] = P.getD j [] := by
  rw [getD_lt _ _ _ (by simp; omega), getD_lt _ _ _ hj, List.getElem_append_left hj]

lemma getD_app_eq (P : List (List ℝ)) (y : ℝ) :
    (P ++ [[y]]).getD P.length [] = [y] := by
  rw [getD_lt _ _ _ (by simp)]
  simp

lemma getD_app_gt (P : List (List ℝ)) (y : ℝ) (j : ℕ) (hj : P.length < j) :
    (P ++ [[y]]).getD j [] = [] := by
  rw [getD_ge _ _ _ (by simp; omega)]

lemma sum_placeAt (P : List (List ℝ)) (c : ℕ) (y : ℝ) (hc : c ≤ P.length) (f : ℕ → ℝ → ℝ) :
    ∑ j ∈ Finset.range (placeAt P c y).length, (((placeAt P c y).getD j []).map (f j)).sum =
      ∑ j ∈ Finset.range P.length, ((P.getD j []).map (f j)).sum + f c y := by
  rcases lt_or_eq_of_le hc with hc | rfl
  · obtain ⟨hl, hg⟩ := placeAt_lt (y := y) hc
    rw [hl]
    have : ∀ j ∈ Finset.range P.length, (((placeAt P c y).getD j []).map (f j)).sum =
        ((P.getD j []).map (f j)).sum + (if j = c then f j y else 0) := by
      intro j _
      rw [hg j]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [hc]
  · rw [placeAt_eq]
    simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [getD_app_lt _ _ _ hj]
    · rw [getD_app_eq]
      simp

lemma ffPack_succ (S : List ℝ) (t : ℕ) (ht : t < S.length) :
    ffPack (S.take (t+1)) =
      placeAt (ffPack (S.take t)) (ffChoice (ffPack (S.take t)) S[t]) S[t] := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some]
  unfold ffPack
  rw [List.foldl_append]
  rfl

lemma ffChoice_le (P : List (List ℝ)) (a : ℝ) : ffChoice P a ≤ P.length := by
  unfold ffChoice; exact List.findIdx_le_length

lemma ffChoice_eq (P : List (List ℝ)) (a : ℝ) (h : ffChoice P a = P.length) :
    ∀ B ∈ P, 1 < B.sum + a := by
  unfold ffChoice at h
  have := List.findIdx_eq_length.mp h
  intro B hB
  have h2 := this B hB
  simp at h2
  linarith

lemma identity (S : List ℝ) (Pf : List (List ℝ)) (t : ℕ) (ht : t ≤ S.length) :
    ∑ j ∈ Finset.range (ffPack (S.take t)).length,
        (((ffPack (S.take t)).getD j []).map (gw (binMax (Pf.getD j [])))).sum =
      ∑ i ∈ Finset.range t, (if h : i < S.length then
          gw (binMax (Pf.getD (ffBinOf S ⟨i, h⟩) [])) S[i] else 0) := by
  induction t with
  | zero => simp [ffPack]
  | succ t ih =>
    have ht' : t < S.length := by omega
    rw [ffPack_succ S t ht', sum_placeAt _ _ _ (ffChoice_le _ _) _, ih (by omega),
      Finset.sum_range_succ, dif_pos ht']
    rfl

structure Inv (S : List ℝ) (t : ℕ) (P : List (List ℝ)) : Prop where
  ne : ∀ j < P.length, P.getD j [] ≠ []
  src : ∀ j, ∀ x ∈ P.getD j [], ∃ i, i < t ∧ ∃ hi : i < S.length, S[i] = x
  full : ∀ j < P.length, 1 ≤ hw (binMax (P.getD j [])) (P.getD j []) ∨
    ∀ j', j < j' → j' < P.length → ⌊1 / binMax (P.getD j' [])⌋₊ ≠ ⌊1 / binMax (P.getD j [])⌋₊

lemma key {B : List ℝ} {y : ℝ} (hne : B ≠ []) (hy : 0 < y) (hy2 : y ≤ 1/2)
    (hge : ∀ x ∈ B, y ≤ x) (hle1 : ∀ x ∈ B, x ≤ 1)
    (htype : ⌊1 / binMax B⌋₊ = ⌊1 / y⌋₊) (hsum : 1 < B.sum + y) :
    1 ≤ hw (binMax B) B := by
  have hpy : IsPiece ⌊1 / y⌋₊ y := piece_of_floor hy (by linarith)
  have hk1 : 1 ≤ ⌊1 / y⌋₊ := piece_pos hpy
  have hkR : (0:ℝ) < (⌊1 / y⌋₊ : ℝ) := by exact_mod_cast hk1
  have hbmem : binMax B ∈ B := binMax_mem hne (fun x hx => le_trans hy.le (hge x hx))
  have hb0 : 0 < binMax B := lt_of_lt_of_le hy (hge _ hbmem)
  have hpb : IsPiece ⌊1 / y⌋₊ (binMax B) := by
    rw [← htype]; exact piece_of_floor hb0 (hle1 _ hbmem)
  have hpx : ∀ x ∈ B, IsPiece ⌊1 / y⌋₊ x := fun x hx =>
    ⟨lt_of_lt_of_le hpy.1 (hge x hx), le_trans (le_binMax hx) hpb.2⟩
  have hg : ∀ x ∈ B, gw (binMax B) x = ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹ := by
    intro x hx
    unfold gw
    rw [if_pos ⟨_, hpx x hx, hpb⟩]
    unfold w1
    rw [floor_eq_of_piece (hpx x hx)]
  have hhw : hw (binMax B) B = B.length * ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹ := by
    unfold hw
    rw [List.map_congr_left hg]
    simp
  have hsumle : B.sum ≤ B.length * ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹ := by
    have := List.sum_le_card_nsmul B (((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹)
      (fun x hx => by have := (hpx x hx).2; simpa [one_div] using this)
    simpa [nsmul_eq_mul] using this
  have hyk : y ≤ ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹ := by simpa [one_div] using hpy.2
  have h1 : ((⌊1 / y⌋₊ : ℝ) - 1) < B.length := by
    have h0 : 1 - ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹ < B.length * ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹ := by linarith
    have h2 : (1 - ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹) * (⌊1 / y⌋₊ : ℝ) = (⌊1 / y⌋₊ : ℝ) - 1 := by
      field_simp
    have h3 : (B.length * ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹) * (⌊1 / y⌋₊ : ℝ) = B.length := by
      field_simp
    have := mul_lt_mul_of_pos_right h0 hkR
    rw [h2, h3] at this
    exact this
  have h4 : ⌊1 / y⌋₊ ≤ B.length := by
    have h5 : ((⌊1 / y⌋₊ : ℕ) : ℝ) < ((B.length + 1 : ℕ) : ℝ) := by push_cast; linarith
    have : ⌊1 / y⌋₊ < B.length + 1 := by exact_mod_cast h5
    omega
  rw [hhw]
  calc (1:ℝ) = (⌊1 / y⌋₊ : ℝ) * ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹ := by field_simp
    _ ≤ B.length * ((⌊1 / y⌋₊ : ℕ) : ℝ)⁻¹ := by gcongr

lemma inv_step (S : List ℝ) (hs : S.Pairwise (fun a b => b ≤ a))
    (hr : ∀ x ∈ S, 0 < x ∧ x ≤ 1/2)
    (t : ℕ) (ht : t < S.length) (P : List (List ℝ)) (hI : Inv S t P) :
    Inv S (t+1) (placeAt P (ffChoice P S[t]) S[t]) := by
  have hyr := hr S[t] (List.getElem_mem ht)
  have hge : ∀ j, ∀ x ∈ P.getD j [], S[t] ≤ x ∧ 0 < x ∧ x ≤ 1/2 := by
    intro j x hx
    obtain ⟨i, hit, hi, rfl⟩ := hI.src j x hx
    exact ⟨List.pairwise_iff_getElem.mp hs i t hi ht hit, hr _ (List.getElem_mem hi)⟩
  have hcle : ffChoice P S[t] ≤ P.length := ffChoice_le _ _
  rcases lt_or_eq_of_le hcle with hlt | heq
  · obtain ⟨hl, hg⟩ := placeAt_lt (y := S[t]) hlt
    have hbm : ∀ j, binMax ((placeAt P (ffChoice P S[t]) S[t]).getD j []) =
        binMax (P.getD j []) := by
      intro j
      rw [hg j]
      split_ifs with hjc
      · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hI.ne j (hjc ▸ hlt))
        exact binMax_append hyr.1.le (le_trans (hge j x hx).1 (le_binMax hx))
      · rfl
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rw [hl] at hj
      rw [hg j]
      split_ifs
      · simp
      · exact hI.ne j hj
    · intro j x hx
      rw [hg j] at hx
      split_ifs at hx
      · rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨i, hit, hi, he⟩ := hI.src j x hx
          exact ⟨i, by omega, hi, he⟩
        · simp at hx
          exact ⟨t, by omega, ht, hx.symm⟩
      · obtain ⟨i, hit, hi, he⟩ := hI.src j x hx
        exact ⟨i, by omega, hi, he⟩
    · intro j hj
      rw [hl] at hj
      simp only [hbm, hl]
      rcases hI.full j hj with h | h
      · left
        rw [hg j]
        split_ifs with hjc
        · rw [hw_append]
          linarith [gw_nonneg (binMax (P.getD j [])) S[t]]
        · exact h
      · right; exact h
  · have hP : placeAt P (ffChoice P S[t]) S[t] = P ++ [[S[t]]] := by
      rw [heq]; exact placeAt_eq
    have hnofit := ffChoice_eq P S[t] heq
    rw [hP]
    have hlen : (P ++ [[S[t]]]).length = P.length + 1 := by simp
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rw [hlen] at hj
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj | rfl
      · rw [getD_app_lt _ _ _ hj]; exact hI.ne j hj
      · rw [getD_app_eq]; simp
    · intro j x hx
      rcases lt_trichotomy j P.length with hj | rfl | hj
      · rw [getD_app_lt _ _ _ hj] at hx
        obtain ⟨i, hit, hi, he⟩ := hI.src j x hx
        exact ⟨i, by omega, hi, he⟩
      · rw [getD_app_eq] at hx
        simp at hx
        exact ⟨t, by omega, ht, hx.symm⟩
      · rw [getD_app_gt _ _ _ hj] at hx
        simp at hx
    · intro j hj
      rw [hlen] at hj
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj | rfl
      · rw [getD_app_lt _ _ _ hj]
        rcases hI.full j hj with h | h
        · left; exact h
        · by_cases htyp : ⌊1 / binMax (P.getD j [])⌋₊ = ⌊1 / S[t]⌋₊
          · left
            have hmem : P.getD j [] ∈ P := by rw [getD_lt _ _ _ hj]; exact List.getElem_mem hj
            exact key (hI.ne j hj) hyr.1 hyr.2 (fun x hx => (hge j x hx).1)
              (fun x hx => by linarith [(hge j x hx).2.2]) htyp (hnofit _ hmem)
          · right
            intro j' hjj' hj'
            rw [hlen] at hj'
            rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj') with hj' | rfl
            · rw [getD_app_lt _ _ _ hj']; exact h j' hjj' hj'
            · rw [getD_app_eq, binMax_single hyr.1.le]
              exact fun e => htyp e.symm
      · right
        intro j' hjj' hj'
        omega

lemma inv_all (S : List ℝ) (hs : S.Pairwise (fun a b => b ≤ a))
    (hr : ∀ x ∈ S, 0 < x ∧ x ≤ 1/2) :
    ∀ t, t ≤ S.length → Inv S t (ffPack (S.take t))
  | 0, _ => by
    refine ⟨?_, ?_, ?_⟩
    · intro j hj; simp [ffPack] at hj
    · intro j x hx; simp [ffPack] at hx
    · intro j hj; simp [ffPack] at hj
  | t+1, ht => by
    rw [ffPack_succ S t (by omega)]
    exact inv_step S hs hr t (by omega) _ (inv_all S hs hr t (by omega))

lemma final_bound (N : ℕ) (hN0 : 0 < N) (S : List ℝ)
    (hr : ∀ x ∈ S, 1/(N:ℝ) < x ∧ x ≤ 1/2) (P : List (List ℝ))
    (hI : Inv S S.length P) :
    (P.length : ℝ) - ∑ j ∈ Finset.Icc 2 (N - 1), ((j : ℝ) - 1) / (j : ℝ) ≤
      ∑ j ∈ Finset.range P.length, ((P.getD j []).map (gw (binMax (P.getD j [])))).sum := by
  have hbin : ∀ j < P.length, binMax (P.getD j []) ∈ P.getD j [] ∧
      1/(N:ℝ) < binMax (P.getD j []) ∧ binMax (P.getD j []) ≤ 1/2 := by
    intro j hj
    have hsrc : ∀ x ∈ P.getD j [], 1/(N:ℝ) < x ∧ x ≤ 1/2 := by
      intro x hx
      obtain ⟨i, _, hi, rfl⟩ := hI.src j x hx
      exact hr _ (List.getElem_mem hi)
    have hm := binMax_mem (hI.ne j hj)
      (fun x hx => le_of_lt (lt_of_le_of_lt (by positivity) (hsrc x hx).1))
    exact ⟨hm, hsrc _ hm⟩
  have hNR : (0:ℝ) < N := by exact_mod_cast hN0
  have hτ : ∀ j < P.length, ⌊1 / binMax (P.getD j [])⌋₊ ∈ Finset.Icc 2 (N - 1) := by
    intro j hj
    obtain ⟨_, h1, h2⟩ := hbin j hj
    have hb : 0 < binMax (P.getD j []) := lt_of_le_of_lt (by positivity) h1
    rw [Finset.mem_Icc]
    constructor
    · apply Nat.le_floor
      rw [le_div_iff₀ hb]
      push_cast
      linarith
    · have : ⌊1 / binMax (P.getD j [])⌋₊ < N := by
        rw [Nat.floor_lt (by positivity)]
        rw [div_lt_iff₀ hb]
        have := (div_lt_iff₀ hNR).mp h1
        nlinarith
      omega
  have hlow : ∀ j < P.length,
      ((⌊1 / binMax (P.getD j [])⌋₊ : ℕ) : ℝ)⁻¹ ≤ hw (binMax (P.getD j [])) (P.getD j []) := by
    intro j hj
    obtain ⟨hm, h1, h2⟩ := hbin j hj
    have hb : 0 < binMax (P.getD j []) := lt_of_le_of_lt (by positivity) h1
    have hpb := piece_of_floor hb (by linarith)
    have hgw : gw (binMax (P.getD j [])) (binMax (P.getD j [])) =
        ((⌊1 / binMax (P.getD j [])⌋₊ : ℕ) : ℝ)⁻¹ := by
      unfold gw
      rw [if_pos ⟨_, hpb, hpb⟩]
      rfl
    rw [← hgw]
    unfold hw
    exact List.single_le_sum (fun x hx => by
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx
      exact gw_nonneg _ _) _ (List.mem_map_of_mem hm)
  classical
  set τ : ℕ → ℕ := fun j => ⌊1 / binMax (P.getD j [])⌋₊ with hτdef
  set Last := (Finset.range P.length).filter
    (fun j => ∀ j', j < j' → j' < P.length → τ j' ≠ τ j) with hLast
  have hper : ∀ j ∈ Finset.range P.length,
      (1:ℝ) - (if j ∈ Last then ((τ j : ℝ) - 1) / (τ j : ℝ) else 0) ≤
        ((P.getD j []).map (gw (binMax (P.getD j [])))).sum := by
    intro j hj
    have hj' : j < P.length := Finset.mem_range.mp hj
    have hτj := Finset.mem_Icc.mp (hτ j hj')
    have hτpos : (0:ℝ) < (τ j : ℝ) := by
      have : 2 ≤ τ j := hτj.1
      have : (2:ℝ) ≤ (τ j : ℝ) := by exact_mod_cast this
      linarith
    split_ifs with hL
    · have := hlow j hj'
      have e : (1:ℝ) - ((τ j : ℝ) - 1) / (τ j : ℝ) = ((τ j : ℕ) : ℝ)⁻¹ := by
        field_simp
        ring
      rw [e]
      exact this
    · rcases hI.full j hj' with h | h
      · simp only [sub_zero]; exact h
      · exact absurd (Finset.mem_filter.mpr ⟨hj, h⟩) hL
  have hsum1 := Finset.sum_le_sum hper
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter] at hsum1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hsum1
  have hfilt : (Finset.range P.length).filter (fun j => j ∈ Last) = Last := by
    ext j; simp [hLast]
  rw [hfilt] at hsum1
  have hinj : Set.InjOn τ Last := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, hLast, Finset.mem_range] at ha hb
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab.symm (ha.2 b h hb.1)
    · exact h
    · exact absurd hab (hb.2 a h ha.1)
  have himg : ∑ j ∈ Last, ((τ j : ℝ) - 1) / (τ j : ℝ) =
      ∑ k ∈ Last.image τ, ((k : ℝ) - 1) / (k : ℝ) := (Finset.sum_image (f := fun k : ℕ => ((k:ℝ) - 1) / (k:ℝ)) hinj).symm
  have hsub : Last.image τ ⊆ Finset.Icc 2 (N - 1) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    exact hτ j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  have hle : ∑ k ∈ Last.image τ, ((k : ℝ) - 1) / (k : ℝ) ≤
      ∑ k ∈ Finset.Icc 2 (N - 1), ((k : ℝ) - 1) / (k : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro k hk _
    have : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have h2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast this
    apply div_nonneg <;> linarith
  linarith

end FFBAux_ffb69a58

open FFBAux_ffb69a58 in
open BinPacking.SmallItems in
theorem ffb_basic_weight_ge (N : ℕ) (hN : 4 ≤ N) (L : List ℝ) (hL : IsList L)
    (hrange : ∀ a ∈ L, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2) :
    ∑ i ∈ basic L, w1 ((sortDesc L).get i) ≥
      (FFD L : ℝ) - ∑ j ∈ Finset.Icc 2 (N - 1), ((j : ℝ) - 1) / (j : ℝ) := by
  have hN0 : 0 < N := by omega
  have hperm : (sortDesc L).Perm L := List.mergeSort_perm _ _
  have hs : (sortDesc L).Pairwise (fun a b => b ≤ a) := by
    have := List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
      (fun a b c h1 h2 => by simp at h1 h2 ⊢; linarith)
      (fun a b => by simp; exact le_total b a) L
    exact this.imp (fun h => by simpa using h)
  have hrS : ∀ x ∈ sortDesc L, 1/(N:ℝ) < x ∧ x ≤ 1/2 :=
    fun x hx => hrange x (hperm.mem_iff.mp hx)
  have hr2 : ∀ x ∈ sortDesc L, 0 < x ∧ x ≤ 1/2 := fun x hx =>
    ⟨lt_of_le_of_lt (by positivity) (hrS x hx).1, (hrS x hx).2⟩
  have hI := inv_all (sortDesc L) hs hr2 (sortDesc L).length le_rfl
  rw [List.take_length] at hI
  have hid := identity (sortDesc L) (ffPack (sortDesc L)) (sortDesc L).length le_rfl
  rw [List.take_length] at hid
  have hfin := final_bound N hN0 (sortDesc L) hrS (ffPack (sortDesc L)) hI
  have hlhs : ∑ i ∈ basic L, w1 ((sortDesc L).get i) =
      ∑ i ∈ Finset.range (sortDesc L).length, (if h : i < (sortDesc L).length then
          gw (binMax ((ffPack (sortDesc L)).getD (ffBinOf (sortDesc L) ⟨i, h⟩) []))
            (sortDesc L)[i] else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => if h : i < (sortDesc L).length then
          gw (binMax ((ffPack (sortDesc L)).getD (ffBinOf (sortDesc L) ⟨i, h⟩) []))
            (sortDesc L)[i] else 0)]
    unfold basic
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    rw [dif_pos i.isLt]
    unfold gw ffdBin ffdPack IsKBin
    simp only [Fin.eta, List.get_eq_getElem]
  have hFFD : (FFD L : ℝ) = ((ffPack (sortDesc L)).length : ℝ) := rfl
  rw [ge_iff_le, hlhs, ← hid, hFFD]
  exact hfin



namespace C4Aux_998ce8a1
open BinPacking.SmallItems

lemma getD_lt {α : Type} (P : List α) (j : ℕ) (d : α) (hj : j < P.length) : P.getD j d = P[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl

lemma getD_ge {α : Type} (P : List α) (j : ℕ) (d : α) (hj : P.length ≤ j) : P.getD j d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]; rfl

lemma getD_placeAt {P : List (List ℝ)} {c : ℕ} {y : ℝ} (hc : c ≤ P.length) (b : ℕ) :
    (placeAt P c y).getD b [] = if b = c then P.getD b [] ++ [y] else P.getD b [] := by
  rcases lt_or_eq_of_le hc with hc | rfl
  · simp only [placeAt, hc, if_true]
    rcases lt_or_ge b P.length with hb | hb
    · rw [getD_lt _ _ _ (by simpa using hb), getD_lt _ _ _ hb, List.getElem_mapIdx]
    · rw [getD_ge _ _ _ (by simpa using hb), getD_ge _ _ _ hb]
      have : b ≠ c := by omega
      simp [this]
  · simp only [placeAt, lt_irrefl, if_false]
    rcases lt_trichotomy b P.length with hb | hb | hb
    · rw [getD_lt _ _ _ (by simp; omega), getD_lt _ _ _ hb, List.getElem_append_left hb]
      simp [Nat.ne_of_lt hb]
    · subst hb
      rw [getD_lt _ _ _ (by simp), getD_ge _ _ _ le_rfl]
      simp
    · rw [getD_ge _ _ _ (by simp; omega), getD_ge _ _ _ (by omega)]
      simp [Nat.ne_of_gt hb]

lemma ffPack_succ (S : List ℝ) (t : ℕ) (ht : t < S.length) :
    ffPack (S.take (t+1)) =
      placeAt (ffPack (S.take t)) (ffChoice (ffPack (S.take t)) S[t]) S[t] := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some]
  unfold ffPack
  rw [List.foldl_append]
  rfl

lemma ffChoice_le (P : List (List ℝ)) (a : ℝ) : ffChoice P a ≤ P.length := by
  unfold ffChoice; exact List.findIdx_le_length

lemma ffChoice_fits (P : List (List ℝ)) (a : ℝ) (h : ffChoice P a < P.length) :
    (P.getD (ffChoice P a) []).sum + a ≤ 1 := by
  unfold ffChoice at h ⊢
  rw [getD_lt _ _ _ h]
  exact of_decide_eq_true (List.findIdx_getElem (w := h))

/-- Bin `b` of the partial packing collects exactly the items whose recorded bin is `b`. -/
lemma binsum (S : List ℝ) (b : ℕ) (t : ℕ) (ht : t ≤ S.length) :
    ∑ i ∈ Finset.range t, (if h : i < S.length then
        (if ffBinOf S ⟨i, h⟩ = b then S[i] else 0) else 0) =
      ((ffPack (S.take t)).getD b []).sum := by
  induction t with
  | zero => simp [ffPack]
  | succ t ih =>
    have ht' : t < S.length := by omega
    rw [Finset.sum_range_succ, ih (by omega), dif_pos ht', ffPack_succ S t ht',
      getD_placeAt (ffChoice_le _ _)]
    have hbin : ffBinOf S ⟨t, ht'⟩ = ffChoice (ffPack (S.take t)) S[t] := rfl
    rw [hbin]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp

/-- Every bin of a first-fit packing has sum at most `1`. -/
lemma bin_le_one (S : List ℝ) (hS : ∀ a ∈ S, a ≤ 1) (t : ℕ) (ht : t ≤ S.length) (b : ℕ) :
    ((ffPack (S.take t)).getD b []).sum ≤ 1 := by
  induction t generalizing b with
  | zero => simp [ffPack]
  | succ t ih =>
    have ht' : t < S.length := by omega
    rw [ffPack_succ S t ht', getD_placeAt (ffChoice_le _ _)]
    split_ifs with hb
    · rw [List.sum_append, List.sum_singleton]
      rcases lt_or_eq_of_le (ffChoice_le (ffPack (S.take t)) S[t]) with hc | hc
      · rw [hb]; exact ffChoice_fits _ _ hc
      · rw [hb, hc, getD_ge _ _ _ le_rfl]
        simpa using hS _ (List.getElem_mem ht')
    · exact ih (by omega) b

lemma fin_binsum_le (S : List ℝ) (hS : ∀ a ∈ S, a ≤ 1) (b : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin S.length => ffBinOf S i = b), S.get i ≤ 1 := by
  rw [Finset.sum_filter]
  have h := binsum S b S.length le_rfl
  rw [List.take_length] at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  have e : ∀ i : Fin S.length, (if ffBinOf S i = b then S.get i else 0) =
      (if h : (i : ℕ) < S.length then
        (if ffBinOf S ⟨i, h⟩ = b then S[(i : ℕ)] else 0) else 0) := by
    intro i
    rw [dif_pos i.isLt]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => e i), h]
  have := bin_le_one S hS S.length le_rfl b
  rwa [List.take_length] at this

lemma piece_pos {k : ℕ} {x : ℝ} (h : IsPiece k x) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨h1, h2⟩ := h
    simp at h1 h2
    linarith
  · exact hk

lemma floor_eq_of_piece {k : ℕ} {x : ℝ} (h : IsPiece k x) : ⌊1 / x⌋₊ = k := by
  have hk := piece_pos h
  obtain ⟨h1, h2⟩ := h
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hx : 0 < x := lt_trans (by positivity) h1
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rw [le_div_iff₀ hx]
    have := (le_div_iff₀ hk').mp h2
    nlinarith
  · rw [div_lt_iff₀ hx]
    have := (div_lt_iff₀ (by positivity : (0:ℝ) < k+1)).mp h1
    nlinarith

lemma piece_of_floor {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : IsPiece ⌊1 / x⌋₊ x := by
  have h1x : (1:ℝ) ≤ 1 / x := by rw [le_div_iff₀ hx]; linarith
  have hk1 : 1 ≤ ⌊1 / x⌋₊ := Nat.le_floor (by simpa using h1x)
  have hk' : (0:ℝ) < (⌊1 / x⌋₊ : ℝ) := by exact_mod_cast hk1
  have hfl : ((⌊1 / x⌋₊ : ℕ) : ℝ) ≤ 1 / x := Nat.floor_le (by positivity)
  have hlt : 1 / x < ((⌊1 / x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  constructor
  · rw [div_lt_iff₀ (by positivity)]
    have := (div_lt_iff₀ hx).mp hlt
    nlinarith
  · rw [le_div_iff₀ hk']
    have := (le_div_iff₀ hx).mp hfl
    nlinarith

lemma le_binMax {x : ℝ} {B : List ℝ} (h : x ∈ B) : x ≤ binMax B := by
  induction B with
  | nil => simp at h
  | cons b B ih =>
    simp only [binMax, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma binMax_mem {B : List ℝ} (hne : B ≠ []) (hpos : ∀ x ∈ B, 0 ≤ x) : binMax B ∈ B := by
  induction B with
  | nil => exact absurd rfl hne
  | cons b B ih =>
    simp only [binMax, List.foldr_cons] at ih ⊢
    by_cases hB : B = []
    · subst hB
      simp [max_eq_left (hpos b (by simp))]
    · rcases max_choice b (B.foldr max 0) with h | h
      · rw [h]; simp
      · rw [h]
        exact List.mem_cons_of_mem _ (ih hB (fun x hx => hpos x (List.mem_cons_of_mem _ hx)))


/-! ### Stage 1: FFD structure facts -/

lemma bin_mem (S : List ℝ) (t : ℕ) (ht : t ≤ S.length) (b : ℕ) (x : ℝ) :
    x ∈ (ffPack (S.take t)).getD b [] ↔
      ∃ p : Fin S.length, (p : ℕ) < t ∧ ffBinOf S p = b ∧ S.get p = x := by
  induction t with
  | zero => simp [ffPack]
  | succ t ih =>
    have ht' : t < S.length := by omega
    rw [ffPack_succ S t ht', getD_placeAt (ffChoice_le _ _)]
    have hbin : ffBinOf S ⟨t, ht'⟩ = ffChoice (ffPack (S.take t)) S[t] := rfl
    split_ifs with hb
    · rw [List.mem_append, ih (by omega), List.mem_singleton]
      constructor
      · rintro (⟨p, hp, hpb, hpx⟩ | hx)
        · exact ⟨p, by omega, hpb, hpx⟩
        · exact ⟨⟨t, ht'⟩, by simp, by rw [hbin, hb], by simp [hx]⟩
      · rintro ⟨p, hp, hpb, hpx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | hp
        · exact Or.inl ⟨p, hp, hpb, hpx⟩
        · right
          have : p = ⟨t, ht'⟩ := Fin.ext hp
          subst this
          rw [← hpx]; simp
    · rw [ih (by omega)]
      constructor
      · rintro ⟨p, hp, hpb, hpx⟩; exact ⟨p, by omega, hpb, hpx⟩
      · rintro ⟨p, hp, hpb, hpx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | hp
        · exact ⟨p, hp, hpb, hpx⟩
        · exfalso
          have : p = ⟨t, ht'⟩ := Fin.ext hp
          subst this
          exact hb (by rw [← hpb, hbin])

lemma binsum_fin (S : List ℝ) (b : ℕ) (t : ℕ) (ht : t ≤ S.length) :
    ((ffPack (S.take t)).getD b []).sum =
      ∑ p ∈ Finset.univ.filter (fun p : Fin S.length => (p : ℕ) < t ∧ ffBinOf S p = b), S.get p := by
  induction t with
  | zero => simp [ffPack]
  | succ t ih =>
    have ht' : t < S.length := by omega
    rw [ffPack_succ S t ht', getD_placeAt (ffChoice_le _ _)]
    have hbin : ffBinOf S ⟨t, ht'⟩ = ffChoice (ffPack (S.take t)) S[t] := rfl
    split_ifs with hb
    · rw [List.sum_append, List.sum_singleton, ih (by omega)]
      have hset : Finset.univ.filter (fun p : Fin S.length => (p : ℕ) < t + 1 ∧ ffBinOf S p = b) =
          insert ⟨t, ht'⟩ (Finset.univ.filter (fun p : Fin S.length => (p : ℕ) < t ∧ ffBinOf S p = b)) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨hp, hpb⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | hp
          · exact Or.inr ⟨hp, hpb⟩
          · exact Or.inl (Fin.ext hp)
        · rintro (rfl | ⟨hp, hpb⟩)
          · exact ⟨by simp, by rw [hbin, hb]⟩
          · exact ⟨by omega, hpb⟩
      rw [hset, Finset.sum_insert (by simp), add_comm]
      simp
    · rw [ih (by omega)]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hp, hpb⟩; exact ⟨by omega, hpb⟩
      · rintro ⟨hp, hpb⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | hp
        · exact ⟨hp, hpb⟩
        · exfalso
          have : p = ⟨t, ht'⟩ := Fin.ext hp
          subst this
          exact hb (by rw [← hpb, hbin])

/-- First fit skipped bin `b` for item `j`: the level of `b` at that time plus `S j` exceeds `1`. -/
lemma skip_sum (S : List ℝ) (j : Fin S.length) (b : ℕ) (hb : b < ffBinOf S j) :
    1 < (∑ p ∈ Finset.univ.filter (fun p : Fin S.length => p < j ∧ ffBinOf S p = b), S.get p)
      + S.get j := by
  have hbl : b < (ffPack (S.take j)).length := lt_of_lt_of_le hb (ffChoice_le _ _)
  have h1 : 1 < ((ffPack (S.take j)).getD b []).sum + S.get j := by
    have hb' : b < ffChoice (ffPack (S.take j)) (S.get j) := hb
    unfold ffChoice at hb'
    rw [getD_lt _ _ _ hbl]
    have h := List.not_of_lt_findIdx hb'
    simp only [decide_eq_false_iff_not, not_le] at h
    exact h
  rw [binsum_fin S b j (le_of_lt j.isLt)] at h1
  have e : Finset.univ.filter (fun p : Fin S.length => (p : ℕ) < (j : ℕ) ∧ ffBinOf S p = b) =
      Finset.univ.filter (fun p : Fin S.length => p < j ∧ ffBinOf S p = b) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Iff.rfl
  rwa [e] at h1

lemma exists_before (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) (j : Fin S.length) (b : ℕ)
    (hb : b < ffBinOf S j) : ∃ p : Fin S.length, p < j ∧ ffBinOf S p = b := by
  have h := skip_sum S j b hb
  have hj := (hS _ (List.get_mem S j)).2
  by_contra hne
  push Not at hne
  have : Finset.univ.filter (fun p : Fin S.length => p < j ∧ ffBinOf S p = b) = ∅ := by
    ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    exact fun ⟨h1, h2⟩ => hne p h1 h2
  rw [this, Finset.sum_empty] at h
  linarith

noncomputable def ty (x : ℝ) : ℕ := ⌊1 / x⌋₊

lemma ty_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : ty y ≤ ty x := by
  unfold ty; exact Nat.floor_le_floor (one_div_le_one_div_of_le hx hxy)

lemma mul_ty_le {x : ℝ} (hx : 0 < x) : x * (ty x : ℝ) ≤ 1 := by
  unfold ty
  have := Nat.floor_le (le_of_lt (one_div_pos.mpr hx))
  have h2 : x * (⌊1 / x⌋₊ : ℝ) ≤ x * (1 / x) := mul_le_mul_of_nonneg_left this hx.le
  rwa [mul_one_div_cancel hx.ne'] at h2

lemma lt_mul_ty_succ {x : ℝ} (hx : 0 < x) : 1 < x * ((ty x : ℝ) + 1) := by
  unfold ty
  have := Nat.lt_floor_add_one (1 / x)
  have h2 : x * (1 / x) < x * ((⌊1 / x⌋₊ : ℝ) + 1) := mul_lt_mul_of_pos_left this hx
  rwa [mul_one_div_cancel hx.ne'] at h2

lemma one_le_ty {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : 1 ≤ ty x := by
  unfold ty
  exact Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hx]; linarith)

lemma get_anti (S : List ℝ) (hs : S.Pairwise (fun a b => b ≤ a)) {p q : Fin S.length}
    (hpq : p ≤ q) : S.get q ≤ S.get p := by
  rcases lt_or_eq_of_le hpq with h | rfl
  · exact List.pairwise_iff_get.mp hs p q h
  · exact le_rfl

lemma lt_of_get_lt (S : List ℝ) (hs : S.Pairwise (fun a b => b ≤ a)) {p q : Fin S.length}
    (h : S.get p < S.get q) : q < p := by
  by_contra hc
  push Not at hc
  exact absurd (get_anti S hs hc) (not_le.mpr h)

/-- Basic in the bin-local sense: no item of the same bin has a smaller type. -/
def isB (S : List ℝ) (i : Fin S.length) : Prop :=
  ∀ p : Fin S.length, ffBinOf S p = ffBinOf S i → ty (S.get i) ≤ ty (S.get p)

lemma isB_same_type (S : List ℝ) {i i' : Fin S.length} (hi : isB S i) (hi' : isB S i')
    (h : ffBinOf S i = ffBinOf S i') : ty (S.get i) = ty (S.get i') :=
  le_antisymm (hi i' h.symm) (hi' i h)

/-- Bins holding basic items of a smaller type come first. -/
lemma bin_lt_of_ty_lt (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) {i j : Fin S.length} (hi : isB S i) (hj : isB S j)
    (hij : ty (S.get i) < ty (S.get j)) : ffBinOf S i < ffBinOf S j := by
  by_contra hc
  push Not at hc
  rcases lt_or_eq_of_le hc with hlt | heq
  · obtain ⟨p, hpi, hpb⟩ := exists_before S hS i (ffBinOf S j) hlt
    have h1 : ty (S.get p) ≤ ty (S.get i) :=
      ty_anti (hS _ (List.get_mem S i)).1 (get_anti S hs hpi.le)
    have h2 := hj p hpb
    omega
  · have := hj i heq.symm
    omega

lemma card_le_of_bin (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) (b c : ℕ)
    (A : Finset (Fin S.length))
    (hA : ∀ p ∈ A, ffBinOf S p = b ∧ 1 / ((c : ℝ) + 1) < S.get p) : A.card ≤ c := by
  have hsub : A ⊆ Finset.univ.filter (fun i : Fin S.length => ffBinOf S i = b) := by
    intro p hp; simp [(hA p hp).1]
  have hsum1 : ∑ p ∈ A, S.get p ≤ 1 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
    · intro p _ _; exact (hS _ (List.get_mem S p)).1.le
    · exact fin_binsum_le S (fun a ha => (hS a ha).2) b
  rcases A.eq_empty_or_nonempty with hE | hne
  · rw [hE]; simp
  have hlow : ∑ _p ∈ A, 1 / ((c : ℝ) + 1) < ∑ p ∈ A, S.get p :=
    Finset.sum_lt_sum_of_nonempty hne (fun p hp => (hA p hp).2)
  rw [Finset.sum_const, nsmul_eq_mul] at hlow
  have hc1 : (0 : ℝ) < (c : ℝ) + 1 := by positivity
  have h := lt_of_lt_of_le hlow hsum1
  rw [mul_one_div, div_lt_one hc1] at h
  have : A.card < c + 1 := by exact_mod_cast h
  omega

/-- Basic items of a later bin of the same type are no larger. -/
lemma later_basic_le (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) {i p : Fin S.length} (hi : isB S i)
    (hty : ty (S.get p) = ty (S.get i)) (hbin : ffBinOf S i < ffBinOf S p) :
    S.get p ≤ S.get i := by
  by_contra hc
  push Not at hc
  have hpi : p < i := lt_of_get_lt S hs hc
  set τ := ty (S.get i) with hτ
  have hxi := (hS _ (List.get_mem S i)).1
  have hxp := (hS _ (List.get_mem S p)).1
  have hτ1 : 1 ≤ τ := one_le_ty hxi (hS _ (List.get_mem S i)).2
  have hτpos : (0 : ℝ) < τ := by exact_mod_cast hτ1
  set R := Finset.univ.filter (fun r : Fin S.length => r < p ∧ ffBinOf S r = ffBinOf S i) with hR
  have hskip := skip_sum S p (ffBinOf S i) hbin
  -- each item of R has size ≤ 1/τ
  have hRle : ∀ r ∈ R, S.get r * τ ≤ 1 := by
    intro r hr
    rw [hR, Finset.mem_filter] at hr
    have h1 := hi r hr.2.2
    have hxr := (hS _ (List.get_mem S r)).1
    have h2 := mul_ty_le hxr
    have h3 : (τ : ℝ) ≤ (ty (S.get r) : ℝ) := by exact_mod_cast h1
    nlinarith
  have hple : S.get p * τ ≤ 1 := by rw [← hty]; exact mul_ty_le hxp
  have hsumR : (∑ r ∈ R, S.get r) * τ ≤ R.card := by
    rw [Finset.sum_mul]
    calc ∑ r ∈ R, S.get r * τ ≤ ∑ _r ∈ R, (1 : ℝ) := Finset.sum_le_sum hRle
      _ = R.card := by simp
  have hcard : τ ≤ R.card := by
    have : (τ : ℝ) < R.card + 1 := by nlinarith
    have : τ < R.card + 1 := by exact_mod_cast this
    omega
  -- R ∪ {i} lies in bin i, all items > 1/(τ+1)
  have hlow_i : 1 / ((τ : ℝ) + 1) < S.get i := by
    have := lt_mul_ty_succ hxi
    rw [div_lt_iff₀ (by positivity)]; linarith
  have hA : ∀ r ∈ insert i R, ffBinOf S r = ffBinOf S i ∧ 1 / ((τ : ℝ) + 1) < S.get r := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact ⟨rfl, hlow_i⟩
    · rw [hR, Finset.mem_filter] at hr
      refine ⟨hr.2.2, lt_of_lt_of_le hlow_i (le_trans hc.le (get_anti S hs hr.2.1.le))⟩
  have hiR : i ∉ R := by
    rw [hR, Finset.mem_filter]; intro h; exact absurd (lt_trans h.2.1 hpi) (lt_irrefl _)
  have := card_le_of_bin S hS (ffBinOf S i) τ (insert i R) hA
  rw [Finset.card_insert_of_notMem hiR] at this
  omega

lemma ty_lt_of_rel (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) {i j : Fin S.length}
    (hrel : (ty (S.get i) : ℝ) * S.get i + S.get j ≤ 1) : ty (S.get i) < ty (S.get j) := by
  have hxi := (hS _ (List.get_mem S i)).1
  have hxj := (hS _ (List.get_mem S j)).1
  have h1 := lt_mul_ty_succ hxi
  have h2 := mul_ty_le hxj
  by_contra hc
  push Not at hc
  have h3 : (ty (S.get j) : ℝ) ≤ ty (S.get i) := by exact_mod_cast hc
  -- S j < 1/(τ+1) and S j * ty j ≤ 1 contradict ty j ≤ τ only via S j > 1/(ty j + 1)
  have h4 := lt_mul_ty_succ hxj
  have h5 : S.get j * ((ty (S.get i) : ℝ) + 1) < 1 := by nlinarith
  nlinarith

/-- (G*) If `i` is basic, a later bin holds a basic item `i'` of the same type, and `j` is basic with
`τ x_i + x_j ≤ 1`, then that later bin contains a non-basic item placed before `j`. -/
lemma gstar (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) {i i' j : Fin S.length} (hi : isB S i) (hi' : isB S i')
    (hj : isB S j) (hty : ty (S.get i') = ty (S.get i)) (hbin : ffBinOf S i < ffBinOf S i')
    (hrel : (ty (S.get i) : ℝ) * S.get i + S.get j ≤ 1) :
    ∃ f : Fin S.length, f < j ∧ ffBinOf S f = ffBinOf S i' ∧ ¬ isB S f := by
  have htj := ty_lt_of_rel S hS hrel
  have hb : ffBinOf S i' < ffBinOf S j := bin_lt_of_ty_lt S hS hs hi' hj (by rw [hty]; exact htj)
  have hskip := skip_sum S j (ffBinOf S i') hb
  by_contra hne
  push Not at hne
  set R := Finset.univ.filter (fun r : Fin S.length => r < j ∧ ffBinOf S r = ffBinOf S i') with hR
  set τ := ty (S.get i)
  have hxi := (hS _ (List.get_mem S i)).1
  have hRB : ∀ r ∈ R, isB S r ∧ ty (S.get r) = τ ∧ S.get r ≤ S.get i := by
    intro r hr
    rw [hR, Finset.mem_filter] at hr
    have hrB := hne r hr.2.1 hr.2.2
    have hrt : ty (S.get r) = τ := by rw [isB_same_type S hrB hi' hr.2.2, hty]
    exact ⟨hrB, hrt, later_basic_le S hS hs hi hrt (by rw [hr.2.2]; exact hbin)⟩
  have hcard : R.card ≤ τ := by
    apply card_le_of_bin S hS (ffBinOf S i') τ R
    intro r hr
    have hr' := hr
    rw [hR, Finset.mem_filter] at hr'
    refine ⟨hr'.2.2, ?_⟩
    have := lt_mul_ty_succ (hS _ (List.get_mem S r)).1
    rw [(hRB r hr).2.1] at this
    rw [div_lt_iff₀ (by positivity)]; linarith
  have hsum : ∑ r ∈ R, S.get r ≤ τ * S.get i := by
    calc ∑ r ∈ R, S.get r ≤ ∑ _r ∈ R, S.get i := Finset.sum_le_sum (fun r hr => (hRB r hr).2.2)
      _ = R.card * S.get i := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ τ * S.get i := by
          apply mul_le_mul_of_nonneg_right _ hxi.le
          exact_mod_cast hcard
  linarith

/-! ### Stage 2a: the cover `pc` (definitions and structural facts) -/

noncomputable def wt (S : List ℝ) (i : Fin S.length) : ℝ := w1 (S.get i)

lemma wt_eq (S : List ℝ) (i : Fin S.length) : wt S i = ((ty (S.get i) : ℕ) : ℝ)⁻¹ := rfl

lemma wt_nonneg (S : List ℝ) (i : Fin S.length) : 0 ≤ wt S i := by
  rw [wt_eq]; positivity

lemma wt_le_one (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) (i : Fin S.length) : wt S i ≤ 1 := by
  rw [wt_eq]
  have h := one_le_ty (hS _ (List.get_mem S i)).1 (hS _ (List.get_mem S i)).2
  have h' : (1 : ℝ) ≤ (ty (S.get i) : ℝ) := by exact_mod_cast h
  exact inv_le_one_of_one_le₀ h'

lemma wt_anti (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) {p q : Fin S.length}
    (h : S.get q ≤ S.get p) : wt S q ≤ wt S p := by
  rw [wt_eq, wt_eq]
  have h1 := ty_anti (hS _ (List.get_mem S q)).1 h
  have h2 := one_le_ty (hS _ (List.get_mem S p)).1 (hS _ (List.get_mem S p)).2
  have h1' : (ty (S.get p) : ℝ) ≤ (ty (S.get q) : ℝ) := by exact_mod_cast h1
  have h2' : (0 : ℝ) < (ty (S.get p) : ℝ) := by exact_mod_cast h2
  exact inv_anti₀ h2' h1'

def Ed (S : List ℝ) (i j : Fin S.length) : Prop :=
  i < j ∧ (ty (S.get i) : ℝ) * S.get i + S.get j ≤ 1

def lastB (S : List ℝ) (i : Fin S.length) : Prop :=
  isB S i ∧ ∀ i' : Fin S.length, isB S i' → ty (S.get i') = ty (S.get i) →
    ffBinOf S i' ≤ ffBinOf S i

open Classical in
noncomputable def tok (S : List ℝ) (N : ℕ) (i : Fin S.length) : ℝ :=
  if ty (S.get i) + 2 ≤ N then wt S i / ((ty (S.get i) : ℝ) + 1) else 0

lemma tok_nonneg (S : List ℝ) (N : ℕ) (i : Fin S.length) : 0 ≤ tok S N i := by
  unfold tok; split_ifs
  · exact div_nonneg (wt_nonneg S i) (by positivity)
  · exact le_rfl

noncomputable def mx {ι : Type} (s : Finset ι) (f : ι → ℝ) : ℝ := s.fold max 0 f

lemma le_mx {ι : Type} {s : Finset ι} {f : ι → ℝ} {j : ι} (hj : j ∈ s) : f j ≤ mx s f := by
  unfold mx; exact (Finset.le_fold_max _).mpr (Or.inr ⟨j, hj, le_rfl⟩)

lemma mx_nonneg {ι : Type} (s : Finset ι) (f : ι → ℝ) : 0 ≤ mx s f := by
  unfold mx; exact (Finset.le_fold_max _).mpr (Or.inl le_rfl)

lemma mx_le {ι : Type} {s : Finset ι} {f : ι → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j ∈ s, f j ≤ c) : mx s f ≤ c := by
  unfold mx; exact (Finset.fold_max_le _).mpr ⟨hc, h⟩

lemma mx_pos {ι : Type} {s : Finset ι} {f : ι → ℝ} (h : 0 < mx s f) :
    ∃ j ∈ s, mx s f ≤ f j := by
  have := (Finset.le_fold_max (s := s) (b := 0) (f := f) (mx s f)).mp le_rfl
  rcases this with h0 | h1
  · exact absurd h0 (not_le.mpr h)
  · exact h1

open Classical in
noncomputable def Fop (S : List ℝ) (N : ℕ) (g : Fin S.length → ℝ) (i : Fin S.length) : ℝ :=
  if lastB S i then tok S N i
  else if isB S i then
    mx (Finset.univ.filter (fun j => isB S j ∧ Ed S i j)) (fun j => wt S i * wt S j - g j)
  else 0

noncomputable def pb (S : List ℝ) (N : ℕ) : Fin S.length → ℝ :=
  (Fop S N)^[S.length] (fun _ => 0)

lemma Fop_local (S : List ℝ) (N : ℕ) (g g' : Fin S.length → ℝ) (i : Fin S.length)
    (h : ∀ j, i < j → g j = g' j) : Fop S N g i = Fop S N g' i := by
  unfold Fop
  split_ifs
  · rfl
  · unfold mx
    apply Finset.fold_congr
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [h j hj.2.1]
  · rfl

lemma iter_stable (S : List ℝ) (N : ℕ) : ∀ (k : ℕ) (i : Fin S.length), S.length - i = k →
    ∀ m, k ≤ m → (Fop S N)^[m] (fun _ => 0) i = (Fop S N)^[m + 1] (fun _ => 0) i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hik m hm
    have hk1 : 1 ≤ k := by have := i.isLt; omega
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    apply Fop_local
    intro j hij
    have hj : S.length - j < k := by
      have := j.isLt; have : (i : ℕ) < j := hij; omega
    exact ih (S.length - j) hj j rfl m' (by have : (i : ℕ) < j := hij; omega)

lemma pb_fix (S : List ℝ) (N : ℕ) (i : Fin S.length) : pb S N i = Fop S N (pb S N) i := by
  unfold pb
  rw [← Function.iterate_succ_apply' (Fop S N)]
  exact iter_stable S N (S.length - i) i rfl S.length (by omega)

lemma pb_lastB (S : List ℝ) (N : ℕ) {i : Fin S.length} (h : lastB S i) : pb S N i = tok S N i := by
  rw [pb_fix]; unfold Fop; rw [if_pos h]

open Classical in
lemma pb_BN (S : List ℝ) (N : ℕ) {i : Fin S.length} (hb : isB S i) (hl : ¬ lastB S i) :
    pb S N i = mx (Finset.univ.filter (fun j => isB S j ∧ Ed S i j))
      (fun j => wt S i * wt S j - pb S N j) := by
  rw [pb_fix]; unfold Fop; rw [if_neg hl, if_pos hb]

lemma pb_nonneg (S : List ℝ) (N : ℕ) (i : Fin S.length) : 0 ≤ pb S N i := by
  rw [pb_fix]; unfold Fop
  split_ifs
  · exact tok_nonneg S N i
  · exact mx_nonneg _ _
  · exact le_rfl

def firstSur (S : List ℝ) (f : Fin S.length) : Prop :=
  ¬ isB S f ∧ ∀ g : Fin S.length, ¬ isB S g → ffBinOf S g = ffBinOf S f → f ≤ g

def nbOK (S : List ℝ) (i : Fin S.length) (b : ℕ) : Prop :=
  (∃ i' : Fin S.length, isB S i' ∧ ty (S.get i') = ty (S.get i) ∧ ffBinOf S i' = b) ∧
    ffBinOf S i < b ∧
    ∀ i' : Fin S.length, isB S i' → ty (S.get i') = ty (S.get i) → ffBinOf S i < ffBinOf S i' →
      b ≤ ffBinOf S i'

lemma nb_exists (S : List ℝ) {i : Fin S.length} (hb : isB S i) (hl : ¬ lastB S i) :
    ∃ b, nbOK S i b := by
  have hex : ∃ b, ∃ i' : Fin S.length, isB S i' ∧ ty (S.get i') = ty (S.get i) ∧
      ffBinOf S i' = b ∧ ffBinOf S i < b := by
    unfold lastB at hl
    push Not at hl
    obtain ⟨i', h1, h2, h3⟩ := hl hb
    exact ⟨_, i', h1, h2, rfl, h3⟩
  classical
  refine ⟨Nat.find hex, ?_, ?_, ?_⟩
  · obtain ⟨i', h1, h2, h3, -⟩ := Nat.find_spec hex
    exact ⟨i', h1, h2, h3⟩
  · obtain ⟨i', -, -, h3, h4⟩ := Nat.find_spec hex
    exact h4
  · intro i' h1 h2 h3
    exact Nat.find_min' hex ⟨i', h1, h2, rfl, h3⟩

lemma nb_unique (S : List ℝ) {i : Fin S.length} {b b' : ℕ} (h : nbOK S i b) (h' : nbOK S i b') :
    b = b' := by
  obtain ⟨⟨i1, h11, h12, h13⟩, h14, h15⟩ := h
  obtain ⟨⟨i2, h21, h22, h23⟩, h24, h25⟩ := h'
  apply le_antisymm
  · have := h15 i2 h21 h22 (by rw [h23]; exact h24); rwa [h23] at this
  · have := h25 i1 h11 h12 (by rw [h13]; exact h14); rwa [h13] at this

lemma firstSur_unique (S : List ℝ) {f f' : Fin S.length} (h : firstSur S f) (h' : firstSur S f')
    (hb : ffBinOf S f = ffBinOf S f') : f = f' :=
  le_antisymm (h.2 f' h'.1 hb.symm) (h'.2 f h.1 hb)

lemma firstSur_exists (S : List ℝ) {g0 : Fin S.length} (hg0 : ¬ isB S g0) :
    ∃ f : Fin S.length, firstSur S f ∧ ffBinOf S f = ffBinOf S g0 ∧ f ≤ g0 := by
  classical
  set T := Finset.univ.filter (fun g : Fin S.length => ¬ isB S g ∧ ffBinOf S g = ffBinOf S g0)
  have hT : T.Nonempty := ⟨g0, by simp [T, hg0]⟩
  obtain ⟨hmem, hmin⟩ := (Finset.min'_mem T hT), (fun g hg => Finset.min'_le T g hg)
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  refine ⟨T.min' hT, ⟨hmem.1, ?_⟩, hmem.2, hmin g0 (by simp [T, hg0])⟩
  intro g hg hgb
  exact hmin g (by simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hg, by rw [hgb, hmem.2]⟩)

lemma target_after (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) {i j : Fin S.length} (hb : isB S i) (hl : ¬ lastB S i)
    (hj : isB S j) (he : Ed S i j) :
    ∃ f : Fin S.length, firstSur S f ∧ nbOK S i (ffBinOf S f) ∧ f < j := by
  obtain ⟨b, hnb⟩ := nb_exists S hb hl
  obtain ⟨⟨i', h1, h2, h3⟩, h4, h5⟩ := hnb
  obtain ⟨f0, hf0j, hf0b, hf0B⟩ := gstar S hS hs hb h1 hj h2 (by rw [h3]; exact h4) he.2
  obtain ⟨f, hf, hfb, hff0⟩ := firstSur_exists S hf0B
  refine ⟨f, hf, ?_, lt_of_le_of_lt hff0 hf0j⟩
  rw [hfb, hf0b, h3]
  exact ⟨⟨i', h1, h2, h3⟩, h4, h5⟩

lemma target_lt (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) {i j f : Fin S.length} (hb : isB S i) (hl : ¬ lastB S i)
    (hj : isB S j) (he : Ed S i j) (hf : firstSur S f) (hnb : nbOK S i (ffBinOf S f)) : f < j := by
  obtain ⟨f', hf', hnb', hlt⟩ := target_after S hS hs hb hl hj he
  have hbb := nb_unique S hnb hnb'
  rw [firstSur_unique S hf hf' hbb]
  exact hlt

open Classical in
noncomputable def fib (S : List ℝ) (f : Fin S.length) : Finset (Fin S.length) :=
  Finset.univ.filter (fun i => isB S i ∧ ¬ lastB S i ∧ firstSur S f ∧ nbOK S i (ffBinOf S f))

lemma mem_fib (S : List ℝ) {f i : Fin S.length} :
    i ∈ fib S f ↔ isB S i ∧ ¬ lastB S i ∧ firstSur S f ∧ nbOK S i (ffBinOf S f) := by
  unfold fib; simp

lemma fib_same (S : List ℝ) {f i1 i2 : Fin S.length} (h1 : i1 ∈ fib S f) (h2 : i2 ∈ fib S f) :
    ty (S.get i1) = ty (S.get i2) ∧ ffBinOf S i1 = ffBinOf S i2 := by
  rw [mem_fib] at h1 h2
  obtain ⟨hb1, -, -, ⟨a1, ha1, ht1, hbn1⟩, hlt1, hmin1⟩ := h1
  obtain ⟨hb2, -, -, ⟨a2, ha2, ht2, hbn2⟩, hlt2, hmin2⟩ := h2
  have hty : ty (S.get i1) = ty (S.get i2) := by
    rw [← ht1, ← ht2]; exact isB_same_type S ha1 ha2 (by rw [hbn1, hbn2])
  refine ⟨hty, ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hmin1 i2 hb2 hty.symm h; omega
  · have := hmin2 i1 hb1 hty h; omega

lemma fib_card (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) {f i0 : Fin S.length}
    (h0 : i0 ∈ fib S f) : (fib S f).card ≤ ty (S.get i0) := by
  apply card_le_of_bin S hS (ffBinOf S i0) (ty (S.get i0))
  intro i hi
  obtain ⟨hty, hbin⟩ := fib_same S hi h0
  refine ⟨hbin, ?_⟩
  have := lt_mul_ty_succ (hS _ (List.get_mem S i)).1
  rw [hty] at this
  rw [div_lt_iff₀ (by positivity)]; linarith

lemma pb_le_fib (S : List ℝ) (N : ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) {f i : Fin S.length} (hi : i ∈ fib S f) :
    pb S N i ≤ wt S i * wt S f := by
  have hi' := (mem_fib S).mp hi
  rw [pb_BN S N hi'.1 hi'.2.1]
  apply mx_le (mul_nonneg (wt_nonneg S i) (wt_nonneg S f))
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  have hfj := target_lt S hS hs hi'.1 hi'.2.1 hj.1 hj.2 hi'.2.2.1 hi'.2.2.2
  have hw : wt S j ≤ wt S f := wt_anti S hS (get_anti S hs hfj.le)
  have := pb_nonneg S N j
  have := mul_le_mul_of_nonneg_left hw (wt_nonneg S i)
  linarith

open Classical in
noncomputable def pc (S : List ℝ) (N : ℕ) (i : Fin S.length) : ℝ :=
  if isB S i then pb S N i else wt S i - ∑ i' ∈ fib S i, pb S N i'

lemma fib_sum_le (S : List ℝ) (N : ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) (f : Fin S.length) :
    ∑ i' ∈ fib S f, pb S N i' ≤ wt S f := by
  rcases (fib S f).eq_empty_or_nonempty with hE | ⟨i0, h0⟩
  · rw [hE, Finset.sum_empty]; exact wt_nonneg S f
  · have hc := fib_card S hS h0
    have hτ := one_le_ty (hS _ (List.get_mem S i0)).1 (hS _ (List.get_mem S i0)).2
    have hτ' : (0 : ℝ) < (ty (S.get i0) : ℝ) := by exact_mod_cast hτ
    calc ∑ i' ∈ fib S f, pb S N i' ≤ ∑ _i' ∈ fib S f, wt S i0 * wt S f := by
          apply Finset.sum_le_sum
          intro i hi
          have := pb_le_fib S N hS hs hi
          rwa [wt_eq S i, (fib_same S hi h0).1, ← wt_eq] at this
      _ = (fib S f).card * (wt S i0 * wt S f) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (ty (S.get i0) : ℝ) * (wt S i0 * wt S f) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (wt_nonneg S i0) (wt_nonneg S f))
          exact_mod_cast hc
      _ = wt S f := by rw [wt_eq S i0]; field_simp

lemma pc_nonneg (S : List ℝ) (N : ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) (i : Fin S.length) : 0 ≤ pc S N i := by
  unfold pc; split_ifs
  · exact pb_nonneg S N i
  · linarith [fib_sum_le S N hS hs i]

/-! ### Stage 2b: every relation edge is covered -/

lemma ty_lt_N (S : List ℝ) (N : ℕ) (hN : 1 ≤ N) (hNS : ∀ a ∈ S, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2)
    (i : Fin S.length) : ty (S.get i) < N := by
  have hx := (hNS _ (List.get_mem S i)).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hxpos : 0 < S.get i := lt_trans (by positivity) hx
  unfold ty
  rw [Nat.floor_lt (by positivity)]
  exact (one_div_lt hxpos hN0).mpr hx

lemma two_le_ty (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1 / 2) (i : Fin S.length) :
    2 ≤ ty (S.get i) := by
  have hx := hS _ (List.get_mem S i)
  unfold ty
  exact Nat.le_floor (by rw [le_div_iff₀ hx.1]; push_cast; linarith [hx.2])

lemma wt_mul_ty (S : List ℝ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) (i : Fin S.length) :
    (ty (S.get i) : ℝ) * wt S i = 1 := by
  rw [wt_eq]
  have h := one_le_ty (hS _ (List.get_mem S i)).1 (hS _ (List.get_mem S i)).2
  have h' : (ty (S.get i) : ℝ) ≠ 0 := by positivity
  field_simp

lemma wt_le_of_ty_ge (S : List ℝ) {i : Fin S.length} {t : ℕ} (h : t + 1 ≤ ty (S.get i)) :
    wt S i ≤ 1 / ((t : ℝ) + 1) := by
  rw [wt_eq, one_div]
  have h' : (t : ℝ) + 1 ≤ (ty (S.get i) : ℝ) := by exact_mod_cast h
  exact inv_anti₀ (by positivity) h'

lemma wt_eq_of_ty (S : List ℝ) {i j : Fin S.length} (h : ty (S.get i) = ty (S.get j)) :
    wt S i = wt S j := by rw [wt_eq, wt_eq, h]

open Classical in
/-- Edges whose first element is basic. -/
lemma edge_basic (S : List ℝ) (N : ℕ) (hN : 1 ≤ N) (hNS : ∀ a ∈ S, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2)
    (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) (hs : S.Pairwise (fun a b => b ≤ a))
    {i j : Fin S.length} (hi : isB S i) (he : Ed S i j) :
    wt S i * wt S j ≤ pc S N i + pc S N j := by
  have hpcj := pc_nonneg S N hS hs j
  have htij := ty_lt_of_rel S hS he.2
  have hpci : pc S N i = pb S N i := by unfold pc; rw [if_pos hi]
  by_cases hl : lastB S i
  · -- E1
    rw [hpci, pb_lastB S N hl]
    have hjN := ty_lt_N S N hN hNS j
    have hle : ty (S.get i) + 2 ≤ N := by omega
    unfold tok; rw [if_pos hle]
    have hwj := wt_le_of_ty_ge S (t := ty (S.get i)) htij
    have : wt S i * wt S j ≤ wt S i / ((ty (S.get i) : ℝ) + 1) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hwj (wt_nonneg S i)
    linarith
  · rw [hpci, pb_BN S N hi hl]
    by_cases hj : isB S j
    · -- E2
      have hpcj' : pc S N j = pb S N j := by unfold pc; rw [if_pos hj]
      have := le_mx (f := fun j => wt S i * wt S j - pb S N j)
        (s := Finset.univ.filter (fun j => isB S j ∧ Ed S i j)) (j := j)
        (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hj, he⟩)
      linarith
    · -- E3
      have hpcj' : pc S N j = wt S j - ∑ i' ∈ fib S j, pb S N i' := by unfold pc; rw [if_neg hj]
      rw [hpcj']
      set M := mx (Finset.univ.filter (fun j => isB S j ∧ Ed S i j))
        (fun j => wt S i * wt S j - pb S N j) with hM
      have hM0 : 0 ≤ M := mx_nonneg _ _
      have hwi1 := wt_le_one S hS i
      have hwj0 := wt_nonneg S j
      set P := (fib S j).filter (fun i' => 0 < pb S N i') with hP
      have hsumP : ∑ i' ∈ fib S j, pb S N i' = ∑ i' ∈ P, pb S N i' := by
        rw [hP, Finset.sum_filter_of_ne]
        intro x _ hx
        exact lt_of_le_of_ne (pb_nonneg S N x) (Ne.symm hx)
      rcases P.eq_empty_or_nonempty with hPe | hPne
      · rw [hsumP, hPe, Finset.sum_empty]
        have : wt S i * wt S j ≤ wt S j := by nlinarith
        linarith
      -- choose maximisers
      have hu : ∀ i' ∈ P, ∃ u : Fin S.length, (isB S u ∧ Ed S i' u) ∧
          pb S N i' ≤ wt S i' * wt S u - pb S N u := by
        intro i' hi'
        rw [hP, Finset.mem_filter] at hi'
        have hi'f := (mem_fib S).mp hi'.1
        have hpos := hi'.2
        rw [pb_BN S N hi'f.1 hi'f.2.1] at hpos ⊢
        obtain ⟨u, hu1, hu2⟩ := mx_pos hpos
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu1
        exact ⟨u, hu1, hu2⟩
      choose! u hu1 hu2 using hu
      obtain ⟨istar, hstarP, hmax⟩ := Finset.exists_max_image P (fun i' => wt S (u i')) hPne
      have hstar_fib : istar ∈ fib S j := (Finset.mem_filter.mp hstarP).1
      have hsf := (mem_fib S).mp hstar_fib
      set us := u istar with hus
      have husB := (hu1 istar hstarP).1
      have hjus : j < us := target_lt S hS hs hsf.1 hsf.2.1 husB (hu1 istar hstarP).2 hsf.2.2.1 hsf.2.2.2
      -- the sum over P
      have hterm : ∀ i' ∈ P, pb S N i' ≤ wt S i' * wt S us - (if i' = istar then pb S N us else 0) := by
        intro i' hi'
        have h1 := hu2 i' hi'
        have h2 := hmax i' hi'
        have h3 := mul_le_mul_of_nonneg_left h2 (wt_nonneg S i')
        split_ifs with h
        · subst h; simpa [hus] using h1
        · have := pb_nonneg S N (u i'); linarith
      have hsum1 : ∑ i' ∈ P, pb S N i' ≤
          ∑ i' ∈ P, wt S i' * wt S us - pb S N us := by
        calc ∑ i' ∈ P, pb S N i'
            ≤ ∑ i' ∈ P, (wt S i' * wt S us - (if i' = istar then pb S N us else 0)) :=
              Finset.sum_le_sum hterm
          _ = ∑ i' ∈ P, wt S i' * wt S us - pb S N us := by
              rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' P istar, if_pos hstarP]
      have hsum2 : ∑ i' ∈ P, wt S i' * wt S us ≤ wt S us := by
        have hcard : P.card ≤ ty (S.get istar) :=
          le_trans (Finset.card_filter_le _ _) (fib_card S hS hstar_fib)
        calc ∑ i' ∈ P, wt S i' * wt S us = ∑ _i' ∈ P, wt S istar * wt S us := by
              apply Finset.sum_congr rfl
              intro i' hi'
              rw [wt_eq_of_ty S (fib_same S (Finset.mem_filter.mp hi').1 hstar_fib).1]
          _ = P.card * (wt S istar * wt S us) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (ty (S.get istar) : ℝ) * (wt S istar * wt S us) := by
              apply mul_le_mul_of_nonneg_right _ (mul_nonneg (wt_nonneg S _) (wt_nonneg S _))
              exact_mod_cast hcard
          _ = wt S us := by rw [← mul_assoc, wt_mul_ty S hS istar, one_mul]
      -- the edge (i, us)
      have hxus : S.get us ≤ S.get j := get_anti S hs hjus.le
      have heus : Ed S i us := ⟨lt_trans he.1 hjus, by linarith [he.2]⟩
      have hMus : wt S i * wt S us - pb S N us ≤ M :=
        le_mx (f := fun j => wt S i * wt S j - pb S N j)
          (s := Finset.univ.filter (fun j => isB S j ∧ Ed S i j)) (j := us)
          (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨husB, heus⟩)
      have hwus : wt S us ≤ wt S j := wt_anti S hS hxus
      rw [hsumP]
      have : wt S i * wt S j ≤ M + (wt S j - (wt S us - pb S N us)) := by
        nlinarith [mul_le_mul_of_nonneg_left hwus (sub_nonneg.mpr hwi1)]
      linarith

open Classical in
/-- Edges whose first element is surplus. -/
lemma edge_surplus (S : List ℝ) (N : ℕ) (hN : 1 ≤ N) (hNS : ∀ a ∈ S, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2)
    (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) (hs : S.Pairwise (fun a b => b ≤ a))
    {i j : Fin S.length} (hi : ¬ isB S i) (he : Ed S i j) :
    wt S i * wt S j ≤ pc S N i + pc S N j := by
  have hpci : pc S N i = wt S i - ∑ i' ∈ fib S i, pb S N i' := by unfold pc; rw [if_neg hi]
  have hpci0 := pc_nonneg S N hS hs i
  have hpcj0 := pc_nonneg S N hS hs j
  have hwi1 := wt_le_one S hS i
  have hwj1 := wt_le_one S hS j
  have hwi0 := wt_nonneg S i
  have hwj0 := wt_nonneg S j
  rcases (fib S i).eq_empty_or_nonempty with hE | ⟨i0, h0⟩
  · rw [hpci, hE, Finset.sum_empty]; nlinarith
  by_cases hjE : ¬ isB S j ∧ fib S j = ∅
  · have : pc S N j = wt S j := by
      unfold pc; rw [if_neg hjE.1, hjE.2, Finset.sum_empty, sub_zero]
    rw [this]; nlinarith
  set t := ty (S.get i) with ht
  set a := wt S i * wt S j - pc S N j with ha
  by_cases ha0 : a ≤ 0
  · linarith
  push Not at ha0
  have hxi := (hS _ (List.get_mem S i)).1
  have hxj := (hS _ (List.get_mem S j)).1
  have htij := ty_lt_of_rel S hS he.2
  have hwj := wt_le_of_ty_ge S (t := t) htij
  have hwit : (t : ℝ) * wt S i = 1 := wt_mul_ty S hS i
  have ht1 : (1 : ℝ) ≤ t := by
    have := one_le_ty hxi (hS _ (List.get_mem S i)).2; exact_mod_cast this
  set c := ty (S.get i0) with hc
  have hc1 : (1 : ℝ) ≤ c := by
    have := one_le_ty (hS _ (List.get_mem S i0)).1 (hS _ (List.get_mem S i0)).2; exact_mod_cast this
  have hwc : (c : ℝ) * wt S i0 = 1 := wt_mul_ty S hS i0
  have hw0 := wt_nonneg S i0
  -- x_j < 1/(t+1)
  have hxj_lt : S.get j * ((t : ℝ) + 1) < 1 := by
    have h1 := lt_mul_ty_succ hxi
    have h2 := he.2
    nlinarith
  set B := max (wt S i0 / ((t : ℝ) + 1)) (wt S i0 * wt S i - a) with hB
  have hB0 : 0 ≤ B := le_trans (div_nonneg hw0 (by positivity)) (le_max_left _ _)
  have hterm : ∀ i' ∈ fib S i, pb S N i' ≤ B := by
    intro i' hi'
    have hi'f := (mem_fib S).mp hi'
    have hwi' : wt S i' = wt S i0 := wt_eq_of_ty S (fib_same S hi' h0).1
    rw [pb_BN S N hi'f.1 hi'f.2.1]
    apply mx_le hB0
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hiu : i < u := target_lt S hS hs hi'f.1 hi'f.2.1 hu.1 hu.2 hi'f.2.2.1 hi'f.2.2.2
    have hxu : S.get u ≤ S.get i := get_anti S hs hiu.le
    have htu : t ≤ ty (S.get u) := ty_anti (hS _ (List.get_mem S u)).1 hxu
    have hpbu := pb_nonneg S N u
    rw [hwi']
    rcases lt_or_eq_of_le htu with hlt | heq
    · have hwu := wt_le_of_ty_ge S (t := t) hlt
      have : wt S i0 * wt S u ≤ wt S i0 / ((t : ℝ) + 1) := by
        rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hwu hw0
      linarith [le_max_left (wt S i0 / ((t : ℝ) + 1)) (wt S i0 * wt S i - a)]
    · -- same type as i: the edge (u, j) is covered by `edge_basic`
      have hwu : wt S u = wt S i := wt_eq_of_ty S heq.symm
      have hxu_low := lt_mul_ty_succ (hS _ (List.get_mem S u)).1
      rw [← heq] at hxu_low
      have huj : u < j := lt_of_get_lt S hs (by nlinarith)
      have heuj : Ed S u j := ⟨huj, by
        rw [← heq]
        have : (t : ℝ) * S.get u ≤ (t : ℝ) * S.get i := mul_le_mul_of_nonneg_left hxu (by positivity)
        linarith [he.2]⟩
      have hcov := edge_basic S N hN hNS hS hs hu.1 heuj
      have hpcu : pc S N u = pb S N u := by unfold pc; rw [if_pos hu.1]
      rw [hpcu, hwu] at hcov
      rw [hwu]
      linarith [le_max_right (wt S i0 / ((t : ℝ) + 1)) (wt S i0 * wt S i - a)]
  have hsum : ∑ i' ∈ fib S i, pb S N i' ≤ c * B := by
    calc ∑ i' ∈ fib S i, pb S N i' ≤ ∑ _i' ∈ fib S i, B := Finset.sum_le_sum hterm
      _ = (fib S i).card * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ c * B := by
          apply mul_le_mul_of_nonneg_right _ hB0
          exact_mod_cast fib_card S hS h0
  have hgoal : a ≤ pc S N i := by
    rw [hpci]
    rcases max_cases (wt S i0 / ((t : ℝ) + 1)) (wt S i0 * wt S i - a) with ⟨hBe, -⟩ | ⟨hBe, -⟩
    · rw [← hB] at hBe
      rw [hBe] at hsum
      have e1 : (c : ℝ) * (wt S i0 / ((t : ℝ) + 1)) = 1 / ((t : ℝ) + 1) := by
        rw [← mul_div_assoc, hwc]
      rw [e1] at hsum
      -- a ≤ wt i * wt j ≤ wt i/(t+1) = wt i - 1/(t+1)
      have h1 : a ≤ wt S i * (1 / ((t : ℝ) + 1)) := by
        have := mul_le_mul_of_nonneg_left hwj hwi0; linarith
      have h2 : wt S i * (1 / ((t : ℝ) + 1)) = wt S i - 1 / ((t : ℝ) + 1) := by
        have ht0 : (t : ℝ) ≠ 0 := by positivity
        have hwi : wt S i = 1 / (t : ℝ) := by field_simp; linarith
        rw [hwi]; field_simp; ring
      linarith
    · rw [← hB] at hBe
      rw [hBe] at hsum
      have e1 : (c : ℝ) * (wt S i0 * wt S i - a) = wt S i - c * a := by
        rw [mul_sub, ← mul_assoc, hwc, one_mul]
      rw [e1] at hsum
      nlinarith
  linarith

lemma edge_cov (S : List ℝ) (N : ℕ) (hN : 1 ≤ N) (hNS : ∀ a ∈ S, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2)
    (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1) (hs : S.Pairwise (fun a b => b ≤ a))
    {i j : Fin S.length} (he : Ed S i j) :
    wt S i * wt S j ≤ pc S N i + pc S N j := by
  by_cases hi : isB S i
  · exact edge_basic S N hN hNS hS hs hi he
  · exact edge_surplus S N hN hNS hS hs hi he

/-! ### Stage 2c: total weight of the cover -/

open Classical in
lemma fib_count (S : List ℝ) (N : ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) (i : Fin S.length) :
    ∑ f : Fin S.length, (if i ∈ fib S f then pb S N i else 0) =
      if isB S i ∧ ¬ lastB S i then pb S N i else 0 := by
  by_cases hBN : isB S i ∧ ¬ lastB S i
  · rw [if_pos hBN]
    rcases eq_or_lt_of_le (pb_nonneg S N i) with h0 | hpos
    · rw [← h0]; simp
    · have hpos' := hpos
      rw [pb_BN S N hBN.1 hBN.2] at hpos'
      obtain ⟨j, hj, -⟩ := mx_pos hpos'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨f, hf, hnb, -⟩ := target_after S hS hs hBN.1 hBN.2 hj.1 hj.2
      have hif : i ∈ fib S f := (mem_fib S).mpr ⟨hBN.1, hBN.2, hf, hnb⟩
      rw [Finset.sum_eq_single f]
      · rw [if_pos hif]
      · intro f' _ hf'
        rw [if_neg]
        intro hif'
        have h' := (mem_fib S).mp hif'
        exact hf' (firstSur_unique S h'.2.2.1 hf (nb_unique S h'.2.2.2 hnb))
      · intro h; exact absurd (Finset.mem_univ f) h
  · rw [if_neg hBN]
    apply Finset.sum_eq_zero
    intro f _
    rw [if_neg]
    intro hif
    have h' := (mem_fib S).mp hif
    exact hBN ⟨h'.1, h'.2.1⟩

open Classical in
lemma sum_fib (S : List ℝ) (N : ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) :
    ∑ f : Fin S.length, ∑ i ∈ fib S f, pb S N i =
      ∑ i : Fin S.length, (if isB S i ∧ ¬ lastB S i then pb S N i else 0) := by
  have h : ∀ f : Fin S.length, ∑ i ∈ fib S f, pb S N i =
      ∑ i : Fin S.length, (if i ∈ fib S f then pb S N i else 0) := by
    intro f
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.sum_congr rfl (fun f _ => h f), Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => fib_count S N hS hs i)

open Classical in
lemma pc_total (S : List ℝ) (N : ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hs : S.Pairwise (fun a b => b ≤ a)) :
    ∑ i, pc S N i = ∑ i, (if lastB S i then tok S N i else 0) +
      ∑ i, (if isB S i then 0 else wt S i) := by
  have hfibB : ∀ f, isB S f → fib S f = ∅ := by
    intro f hf
    ext i
    simp only [Finset.notMem_empty, iff_false]
    intro hi
    exact ((mem_fib S).mp hi).2.2.1.1 hf
  have e1 : ∀ i, pc S N i = (if lastB S i then tok S N i else 0) + (if isB S i then 0 else wt S i)
      + (if isB S i ∧ ¬ lastB S i then pb S N i else 0) - ∑ i' ∈ fib S i, pb S N i' := by
    intro i
    unfold pc
    by_cases hb : isB S i
    · rw [hfibB i hb, Finset.sum_empty, if_pos hb, if_pos hb]
      by_cases hl : lastB S i
      · rw [if_pos hl, if_neg (fun h => h.2 hl), pb_lastB S N hl]; ring
      · rw [if_neg hl, if_pos ⟨hb, hl⟩]; ring
    · have hl : ¬ lastB S i := fun h => hb h.1
      rw [if_neg hb, if_neg hb, if_neg hl, if_neg (fun h => hb h.1)]; ring
  rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, sum_fib S N hS hs]
  ring

open Classical in
lemma tok_total (S : List ℝ) (N : ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 1)
    (hS2 : ∀ a ∈ S, 0 < a ∧ a ≤ 1 / 2) :
    ∑ i, (if lastB S i then tok S N i else 0) ≤ ∑ j ∈ Finset.Icc 3 (N - 1), 1 / (j : ℝ) := by
  rw [← Finset.sum_filter]
  set T := Finset.univ.filter (fun i => lastB S i) with hTdef
  have hT : ∑ i ∈ T, tok S N i = ∑ i ∈ T.filter (fun i => ty (S.get i) + 2 ≤ N), tok S N i := by
    rw [Finset.sum_filter (fun i => ty (S.get i) + 2 ≤ N) (fun i => tok S N i)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : ty (S.get i) + 2 ≤ N
    · rw [if_pos h]
    · rw [if_neg h]; unfold tok; rw [if_neg h]
  rw [hT]
  set T' := T.filter (fun i => ty (S.get i) + 2 ≤ N) with hT'
  have hmaps : ∀ i ∈ T', ty (S.get i) ∈ Finset.Icc 2 (N - 2) := by
    intro i hi
    simp only [hT', hTdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact Finset.mem_Icc.mpr ⟨two_le_ty S hS2 i, by omega⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber : ∀ k ∈ Finset.Icc 2 (N - 2),
      ∑ i ∈ T'.filter (fun i => ty (S.get i) = k), tok S N i ≤ 1 / ((k : ℝ) + 1) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    set Fk := T'.filter (fun i => ty (S.get i) = k) with hFk
    have hmemF : ∀ i ∈ Fk, lastB S i ∧ ty (S.get i) + 2 ≤ N ∧ ty (S.get i) = k := by
      intro i hi
      simp only [hFk, hT', hTdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact ⟨hi.1.1, hi.1.2, hi.2⟩
    have hterm : ∀ i ∈ Fk, tok S N i = 1 / (k : ℝ) / ((k : ℝ) + 1) := by
      intro i hi
      obtain ⟨-, h2, h3⟩ := hmemF i hi
      unfold tok
      rw [if_pos h2, wt_eq, h3, one_div]
    have hcard : Fk.card ≤ k := by
      rcases Fk.eq_empty_or_nonempty with hE | ⟨i0, hi0⟩
      · rw [hE]; simp
      · apply card_le_of_bin S hS (ffBinOf S i0) k
        intro i hi
        obtain ⟨hl, -, hik⟩ := hmemF i hi
        obtain ⟨hl0, -, hi0k⟩ := hmemF i0 hi0
        refine ⟨le_antisymm (hl0.2 i hl.1 (by rw [hik, hi0k]))
          (hl.2 i0 hl0.1 (by rw [hik, hi0k])), ?_⟩
        have := lt_mul_ty_succ (hS _ (List.get_mem S i)).1
        rw [hik] at this
        rw [div_lt_iff₀ (by positivity)]; linarith
    calc ∑ i ∈ Fk, tok S N i = ∑ _i ∈ Fk, 1 / (k : ℝ) / ((k : ℝ) + 1) := Finset.sum_congr rfl hterm
      _ = Fk.card * (1 / (k : ℝ) / ((k : ℝ) + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ k * (1 / (k : ℝ) / ((k : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard); positivity
      _ = 1 / ((k : ℝ) + 1) := by field_simp
  refine le_trans (Finset.sum_le_sum hfiber) (le_of_eq ?_)
  refine Finset.sum_nbij' (fun k => k + 1) (fun j => j - 1) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
  · intro k _; simp
  · intro j hj; simp only [Finset.mem_Icc] at hj; omega
  · intro k _; push_cast; ring

/-! ### Stage 2d: assembly -/

open Classical in
lemma basic_iff (L : List ℝ) (hS : ∀ a ∈ sortDesc L, 0 < a ∧ a ≤ 1)
    (i : Fin (sortDesc L).length) : i ∈ basic L ↔ isB (sortDesc L) i := by
  have hmem : ∀ x, x ∈ (ffPack (sortDesc L)).getD (ffBinOf (sortDesc L) i) [] ↔
      ∃ p : Fin (sortDesc L).length, ffBinOf (sortDesc L) p = ffBinOf (sortDesc L) i ∧
        (sortDesc L).get p = x := by
    intro x
    have h := bin_mem (sortDesc L) (sortDesc L).length le_rfl (ffBinOf (sortDesc L) i) x
    rw [List.take_length] at h
    rw [h]
    constructor
    · rintro ⟨p, -, h1, h2⟩; exact ⟨p, h1, h2⟩
    · rintro ⟨p, h1, h2⟩; exact ⟨p, p.isLt, h1, h2⟩
  have hiB : (sortDesc L).get i ∈ (ffPack (sortDesc L)).getD (ffBinOf (sortDesc L) i) [] :=
    (hmem _).mpr ⟨i, rfl, rfl⟩
  have hne : (ffPack (sortDesc L)).getD (ffBinOf (sortDesc L) i) [] ≠ [] := by
    intro h; rw [h] at hiB; simp at hiB
  have hpos : ∀ x ∈ (ffPack (sortDesc L)).getD (ffBinOf (sortDesc L) i) [], 0 ≤ x := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := (hmem x).mp hx
    exact (hS _ (List.get_mem _ p)).1.le
  obtain ⟨g, hg1, hg2⟩ := (hmem _).mp (binMax_mem hne hpos)
  have hmaxle : ∀ p : Fin (sortDesc L).length, ffBinOf (sortDesc L) p = ffBinOf (sortDesc L) i →
      (sortDesc L).get p ≤ (sortDesc L).get g := by
    intro p hp
    rw [hg2]; exact le_binMax ((hmem _).mpr ⟨p, hp, rfl⟩)
  unfold basic
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  unfold ffdBin ffdPack IsKBin
  constructor
  · rintro ⟨k, hk1, hk2⟩ p hp
    rw [← hg2] at hk2
    have e1 : ty ((sortDesc L).get i) = k := floor_eq_of_piece hk1
    have e2 : ty ((sortDesc L).get g) = k := floor_eq_of_piece hk2
    have := ty_anti (hS _ (List.get_mem _ p)).1 (hmaxle p hp)
    omega
  · intro h
    refine ⟨ty ((sortDesc L).get i), piece_of_floor (hS _ (List.get_mem _ i)).1
      (hS _ (List.get_mem _ i)).2, ?_⟩
    rw [← hg2]
    have h1 : ty ((sortDesc L).get i) ≤ ty ((sortDesc L).get g) := h g hg1
    have h2 : ty ((sortDesc L).get g) ≤ ty ((sortDesc L).get i) :=
      ty_anti (hS _ (List.get_mem _ i)).1 (hmaxle i rfl)
    have e : ty ((sortDesc L).get i) = ty ((sortDesc L).get g) := le_antisymm h1 h2
    rw [e]
    exact piece_of_floor (hS _ (List.get_mem _ g)).1 (hS _ (List.get_mem _ g)).2

/-- The piece type `k` is positive whenever `x` obeys relation `k` with something. -/
lemma rel_k_pos {k : ℕ} {x y : ℝ} (h : ObeysRelation k x y) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    obtain ⟨⟨h1, h2⟩, _⟩ := h
    simp at h1 h2
    linarith
  · exact hk

open Classical in
lemma w2_eq (x y : ℝ) :
    w2 x y = w1 x + w1 y -
      (if ObeysRelation ⌊1 / x⌋₊ x y then w1 y / (⌊1 / x⌋₊ : ℝ) else 0) := by
  unfold w2
  split_ifs with h
  · have hk : (1 : ℝ) ≤ (⌊1 / x⌋₊ : ℝ) := by exact_mod_cast rel_k_pos h
    field_simp
    ring
  · ring

open Classical in
/-- (ID): `w₁₂` equals the total `w₁` weight minus the relation-pair losses. -/
lemma w12_eq (S : List ℝ) (σ : Equiv.Perm (Fin S.length)) (hσ : σ * σ = 1) :
    w12 S σ = ∑ i, w1 (S.get i) -
      ∑ i ∈ Finset.univ.filter (fun i => i < σ i ∧
          ObeysRelation ⌊1 / S.get i⌋₊ (S.get i) (S.get (σ i))),
        w1 (S.get (σ i)) / (⌊1 / S.get i⌋₊ : ℝ) := by
  have hinv : ∀ i, σ (σ i) = i := fun i => by
    have := congrArg (fun τ : Equiv.Perm (Fin S.length) => τ i) hσ
    simpa [Equiv.Perm.mul_apply] using this
  unfold w12
  simp_rw [w2_eq]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_filter]
  -- the image of `i < σ i` under `σ` is `σ i < i`
  have hswap : ∑ i ∈ Finset.univ.filter (fun i => i < σ i), w1 (S.get (σ i)) =
      ∑ i ∈ Finset.univ.filter (fun i => σ i < i), w1 (S.get i) := by
    refine Finset.sum_nbij' (fun i => σ i) (fun i => σ i) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [hinv]; exact hi
    · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [hinv]; exact hi
    · intro i _; exact hinv i
    · intro i _; exact hinv i
    · intro i _; rfl
  rw [hswap]
  have hsplit : ∑ i, w1 (S.get i) =
      (∑ i ∈ Finset.univ.filter (fun i => σ i = i), w1 (S.get i)) +
      ((∑ i ∈ Finset.univ.filter (fun i => i < σ i), w1 (S.get i)) +
        ∑ i ∈ Finset.univ.filter (fun i => σ i < i), w1 (S.get i)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => σ i = i)]
    congr 1
    rw [← Finset.sum_union]
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro h
        rcases lt_trichotomy i (σ i) with h1 | h1 | h1
        · exact Or.inl h1
        · exact absurd h1.symm h
        · exact Or.inr h1
      · rintro (h | h)
        · exact fun he => by rw [he] at h; exact lt_irrefl _ h
        · exact fun he => by rw [he] at h; exact lt_irrefl _ h
    · rw [Finset.disjoint_filter]
      intro i _ h1 h2
      exact lt_asymm h1 h2
  rw [hsplit, Finset.filter_filter]
  ring


open Classical in
theorem main (N : ℕ) (hN : 4 ≤ N) (L : List ℝ)
    (hrange : ∀ a ∈ L, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2)
    (σ : Equiv.Perm (Fin (sortDesc L).length)) (hσ : σ ∈ pairings (sortDesc L).length) :
    w12 (sortDesc L) σ ≥
      ∑ i ∈ basic L, w1 ((sortDesc L).get i) - ∑ j ∈ Finset.Icc 3 (N - 1), 1 / (j : ℝ) := by
  have hperm : (sortDesc L).Perm L := List.mergeSort_perm _ _
  have hs : (sortDesc L).Pairwise (fun a b => b ≤ a) := by
    have := List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
      (fun a b c h1 h2 => by simp at h1 h2 ⊢; linarith)
      (fun a b => by simp; exact le_total b a) L
    exact this.imp (fun h => by simpa using h)
  have hNS : ∀ a ∈ sortDesc L, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2 :=
    fun a ha => hrange a (hperm.mem_iff.mp ha)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hS2 : ∀ a ∈ sortDesc L, 0 < a ∧ a ≤ 1 / 2 :=
    fun a ha => ⟨lt_trans (by positivity) (hNS a ha).1, (hNS a ha).2⟩
  have hS : ∀ a ∈ sortDesc L, 0 < a ∧ a ≤ 1 :=
    fun a ha => ⟨(hS2 a ha).1, by linarith [(hS2 a ha).2]⟩
  have hσ' : σ * σ = 1 := (Finset.mem_filter.mp hσ).2
  have hinv : ∀ i, σ (σ i) = i := fun i => by
    have := congrArg (fun τ : Equiv.Perm (Fin (sortDesc L).length) => τ i) hσ'
    simpa [Equiv.Perm.mul_apply] using this
  rw [w12_eq (sortDesc L) σ hσ']
  set R := Finset.univ.filter (fun i => i < σ i ∧
      ObeysRelation ⌊1 / (sortDesc L).get i⌋₊ ((sortDesc L).get i) ((sortDesc L).get (σ i))) with hR
  have hdisj : Disjoint R (R.image σ) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨b, hbR, rfl⟩ := Finset.mem_image.mp hb
    rw [hR, Finset.mem_filter] at ha hbR
    have h1 := hbR.2.1
    have h2 := ha.2.1
    rw [hinv] at h2
    exact absurd (lt_trans h1 h2) (lt_irrefl _)
  have hloss : ∑ i ∈ R, w1 ((sortDesc L).get (σ i)) / (⌊1 / (sortDesc L).get i⌋₊ : ℝ) ≤
      ∑ i, pc (sortDesc L) N i := by
    have h1 : ∀ i ∈ R, w1 ((sortDesc L).get (σ i)) / (⌊1 / (sortDesc L).get i⌋₊ : ℝ) ≤
        pc (sortDesc L) N i + pc (sortDesc L) N (σ i) := by
      intro i hi
      rw [hR, Finset.mem_filter] at hi
      have he : Ed (sortDesc L) i (σ i) := ⟨hi.2.1, hi.2.2.2⟩
      have hc := edge_cov (sortDesc L) N (by omega) hNS hS hs he
      have e : w1 ((sortDesc L).get (σ i)) / (⌊1 / (sortDesc L).get i⌋₊ : ℝ) =
          wt (sortDesc L) i * wt (sortDesc L) (σ i) := by
        unfold wt w1; ring
      rw [e]; exact hc
    calc ∑ i ∈ R, w1 ((sortDesc L).get (σ i)) / (⌊1 / (sortDesc L).get i⌋₊ : ℝ)
        ≤ ∑ i ∈ R, (pc (sortDesc L) N i + pc (sortDesc L) N (σ i)) := Finset.sum_le_sum h1
      _ = ∑ i ∈ R, pc (sortDesc L) N i + ∑ i ∈ R.image σ, pc (sortDesc L) N i := by
          rw [Finset.sum_add_distrib, Finset.sum_image (fun a _ b _ h => σ.injective h)]
      _ = ∑ i ∈ R ∪ R.image σ, pc (sortDesc L) N i := by rw [Finset.sum_union hdisj]
      _ ≤ ∑ i, pc (sortDesc L) N i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => pc_nonneg (sortDesc L) N hS hs i)
  have htot := pc_total (sortDesc L) N hS hs
  have htok := tok_total (sortDesc L) N hS hS2
  have hbasic : basic L = Finset.univ.filter (fun i => isB (sortDesc L) i) := by
    ext i
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    exact basic_iff L hS i
  have hsplit : ∑ i, w1 ((sortDesc L).get i) =
      ∑ i ∈ basic L, w1 ((sortDesc L).get i) +
        ∑ i, (if isB (sortDesc L) i then 0 else wt (sortDesc L) i) := by
    rw [hbasic, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold wt
    split_ifs <;> ring
  linarith

end C4Aux_998ce8a1


namespace WFFD_9ce81529
open BinPacking.SmallItems

lemma harmonic_bound (N : ℕ) (hN : 4 ≤ N) :
    ∑ j ∈ Finset.Icc 2 (N - 1), ((j : ℝ) - 1) / (j : ℝ) +
      ∑ j ∈ Finset.Icc 3 (N - 1), 1 / (j : ℝ) ≤ (N : ℝ) - 2 := by
  have hins : Finset.Icc 2 (N - 1) = insert 2 (Finset.Icc 3 (N - 1)) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hins, Finset.sum_insert (by simp), add_assoc, ← Finset.sum_add_distrib]
  have h1 : ∀ j ∈ Finset.Icc 3 (N - 1), ((j : ℝ) - 1) / (j : ℝ) + 1 / (j : ℝ) = 1 := by
    intro j hj
    have hj3 : 3 ≤ j := (Finset.mem_Icc.mp hj).1
    have : (j : ℝ) ≠ 0 := by positivity
    field_simp; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  have e : ((N - 1 + 1 - 3 : ℕ) : ℝ) = (N : ℝ) - 3 := by
    rw [show N - 1 + 1 - 3 = N - 3 by omega, Nat.cast_sub (by omega : 3 ≤ N)]; norm_num
  have e2 : (((2 : ℕ) : ℝ) - 1) / ((2 : ℕ) : ℝ) = 1 / 2 := by norm_num
  rw [e, e2]
  linarith

theorem W_ge (N : ℕ) (hN : 4 ≤ N) (L : List ℝ) (hL : IsList L)
    (hrange : ∀ a ∈ L, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2) :
    W L ≥ (FFD L : ℝ) - (N : ℝ) + 2 := by
  have hA := ffb_basic_weight_ge N hN L hL hrange
  have hH := harmonic_bound N hN
  unfold W
  rw [ge_iff_le]
  apply Finset.le_inf'
  intro σ hσ
  have hB := C4Aux_998ce8a1.main N hN L hrange σ hσ
  linarith

end WFFD_9ce81529

namespace FFDAux_e3877310
open BinPacking.SmallItems

lemma getD_lt {α : Type} (P : List α) (j : ℕ) (d : α) (hj : j < P.length) : P.getD j d = P[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl

lemma getD_ge {α : Type} (P : List α) (j : ℕ) (d : α) (hj : P.length ≤ j) : P.getD j d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]; rfl

lemma placeAt_lt {P : List (List ℝ)} {c : ℕ} {y : ℝ} (hc : c < P.length) :
    (placeAt P c y).length = P.length ∧
    ∀ j, (placeAt P c y).getD j [] = if j = c then P.getD j [] ++ [y] else P.getD j [] := by
  refine ⟨by simp [placeAt, hc], fun j => ?_⟩
  simp only [placeAt, hc, if_true]
  rcases lt_or_ge j P.length with hj | hj
  · rw [getD_lt _ _ _ (by simpa using hj), getD_lt _ _ _ hj, List.getElem_mapIdx]
  · rw [getD_ge _ _ _ (by simpa using hj), getD_ge _ _ _ hj]
    have : j ≠ c := by omega
    simp [this]

lemma placeAt_eq {P : List (List ℝ)} {y : ℝ} :
    placeAt P P.length y = P ++ [[y]] := by simp [placeAt]

lemma getD_app_lt (P : List (List ℝ)) (y : ℝ) (j : ℕ) (hj : j < P.length) :
    (P ++ [[y]]).getD j [] = P.getD j [] := by
  rw [getD_lt _ _ _ (by simp; omega), getD_lt _ _ _ hj, List.getElem_append_left hj]

lemma getD_app_eq (P : List (List ℝ)) (y : ℝ) :
    (P ++ [[y]]).getD P.length [] = [y] := by
  rw [getD_lt _ _ _ (by simp)]
  simp

lemma sum_placeAt (P : List (List ℝ)) (c : ℕ) (y : ℝ) (hc : c ≤ P.length) (f : ℕ → ℝ → ℝ) :
    ∑ j ∈ Finset.range (placeAt P c y).length, (((placeAt P c y).getD j []).map (f j)).sum =
      ∑ j ∈ Finset.range P.length, ((P.getD j []).map (f j)).sum + f c y := by
  rcases lt_or_eq_of_le hc with hc | rfl
  · obtain ⟨hl, hg⟩ := placeAt_lt (y := y) hc
    rw [hl]
    have : ∀ j ∈ Finset.range P.length, (((placeAt P c y).getD j []).map (f j)).sum =
        ((P.getD j []).map (f j)).sum + (if j = c then f j y else 0) := by
      intro j _
      rw [hg j]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [hc]
  · rw [placeAt_eq]
    simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [getD_app_lt _ _ _ hj]
    · rw [getD_app_eq]
      simp

lemma ffChoice_le (P : List (List ℝ)) (a : ℝ) : ffChoice P a ≤ P.length := by
  unfold ffChoice; exact List.findIdx_le_length

lemma ffChoice_eq (P : List (List ℝ)) (a : ℝ) (h : ffChoice P a = P.length) :
    ∀ B ∈ P, 1 < B.sum + a := by
  unfold ffChoice at h
  have := List.findIdx_eq_length.mp h
  intro B hB
  have h2 := this B hB
  simp at h2
  linarith

/-- total content of a list of bins -/
noncomputable def tot (P : List (List ℝ)) : ℝ :=
  ∑ j ∈ Finset.range P.length, ((P.getD j []).map (fun x : ℝ => x)).sum

lemma tot_placeAt (P : List (List ℝ)) (c : ℕ) (a : ℝ) (hc : c ≤ P.length) :
    tot (placeAt P c a) = tot P + a :=
  sum_placeAt P c a hc (fun _ x => x)

noncomputable def step (bins : List (List ℝ)) (a : ℝ) : List (List ℝ) :=
  placeAt bins (ffChoice bins a) a

lemma tot_fold : ∀ (B : List ℝ) (P : List (List ℝ)),
    tot (B.foldl step P) = tot P + B.sum
  | [], P => by simp
  | a :: B, P => by
    rw [List.foldl_cons, tot_fold B, step, tot_placeAt _ _ _ (ffChoice_le _ _), List.sum_cons]
    ring

lemma tot_ge (r : ℝ) (P : List (List ℝ)) (hP : ∀ B ∈ P, 1 < r * B.sum) :
    (P.length : ℝ) ≤ r * tot P := by
  unfold tot
  rw [Finset.mul_sum]
  calc (P.length : ℝ) = ∑ _j ∈ Finset.range P.length, (1 : ℝ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_range] at hj
      rw [getD_lt _ _ _ hj, List.map_id']
      exact (hP _ (List.getElem_mem hj)).le

lemma small_phase (r : ℝ) (hr : 0 < r) (n0 : ℕ) : ∀ (B : List ℝ) (P : List (List ℝ)),
    (∀ a ∈ B, 0 < a ∧ r * a ≤ r - 1) →
    (P.length = n0 ∨ (P.length : ℝ) - 1 < r * tot P) →
    ((B.foldl step P).length = n0 ∨ ((B.foldl step P).length : ℝ) - 1 < r * tot (B.foldl step P))
  | [], P, _, hP => by simpa using hP
  | a :: B, P, hB, hP => by
    rw [List.foldl_cons]
    apply small_phase r hr n0 B
    · exact fun x hx => hB x (List.mem_cons_of_mem _ hx)
    · obtain ⟨ha0, ha1⟩ := hB a List.mem_cons_self
      have htot : tot (step P a) = tot P + a := tot_placeAt _ _ _ (ffChoice_le _ _)
      rcases lt_or_eq_of_le (ffChoice_le P a) with hc | hc
      · have hl : (step P a).length = P.length := (placeAt_lt (y := a) hc).1
        rw [hl, htot]
        rcases hP with hP | hP
        · exact Or.inl hP
        · right; nlinarith
      · right
        have hfull := ffChoice_eq P a hc
        have hge : (P.length : ℝ) ≤ r * tot P := by
          apply tot_ge r P
          intro B hBm
          have := hfull B hBm
          nlinarith
        have hl : (step P a).length = P.length + 1 := by
          unfold step; rw [hc, placeAt_eq]; simp
        rw [hl, htot]
        push_cast
        nlinarith

lemma split_sorted (t : ℝ) : ∀ S : List ℝ, S.Pairwise (fun a b => b ≤ a) →
    S = S.filter (fun a => decide (t < a)) ++ S.filter (fun a => !decide (t < a))
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.pairwise_cons] at h
    by_cases hx : t < x
    · have ih := split_sorted t xs h.2
      simp only [List.filter_cons, hx, decide_true, if_true, Bool.not_true]
      simp only [Bool.false_eq_true, if_false, List.cons_append]
      exact congrArg (x :: ·) ih
    · have h1 : xs.filter (fun a => decide (t < a)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        have := h.1 y hy
        simp only [decide_eq_true_eq]
        intro hty; exact hx (lt_of_lt_of_le hty this)
      have h2 : xs.filter (fun a => !decide (t < a)) = xs := by
        rw [List.filter_eq_self]
        intro y hy
        have := h.1 y hy
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
        intro hty; exact hx (lt_of_lt_of_le hty this)
      simp only [List.filter_cons, hx, decide_false, Bool.false_eq_true, if_false, Bool.not_false,
        if_true, h1, h2, List.nil_append]

lemma opt_nonempty (L : List ℝ) (hL : IsList L) : {b : ℕ | ∃ f : Fin L.length → Fin b,
    ∀ j : Fin b, ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i ≤ 1}.Nonempty := by
  refine ⟨L.length, fun i => i, ?_⟩
  intro j
  have : Finset.univ.filter (fun i : Fin L.length => i = j) = {j} := by
    ext x; simp
  rw [this, Finset.sum_singleton]
  exact (hL _ (List.get_mem L j)).2

lemma sum_le_optBins (L : List ℝ) (hL : IsList L) : L.sum ≤ (optBins L : ℝ) := by
  obtain ⟨f, hf⟩ := Nat.sInf_mem (opt_nonempty L hL)
  have hsum : L.sum = ∑ i : Fin L.length, L.get i := by
    rw [← List.sum_ofFn, List.ofFn_get]
  unfold optBins
  rw [hsum, ← Finset.sum_fiberwise Finset.univ f (fun i => L.get i)]
  calc _ ≤ ∑ _j : Fin (sInf {b : ℕ | ∃ f : Fin L.length → Fin b, ∀ j : Fin b,
        ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i ≤ 1}), (1 : ℝ) :=
        Finset.sum_le_sum (fun j _ => hf j)
    _ = _ := by simp

lemma optBins_mono (L : List ℝ) (hL : IsList L) (p : ℝ → Bool) :
    optBins (L.filter p) ≤ optBins L := by
  obtain ⟨f, hf⟩ := Nat.sInf_mem (opt_nonempty L hL)
  obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp (List.filter_sublist (p := p) (l := L))
  unfold optBins
  apply Nat.sInf_le
  refine ⟨fun i => f (e i), fun j => ?_⟩
  calc ∑ i ∈ Finset.univ.filter (fun i => f (e i) = j), (L.filter p).get i
      = ∑ i ∈ (Finset.univ.filter (fun i => f (e i) = j)).map e.toEmbedding, L.get i := by
        rw [Finset.sum_map]; exact Finset.sum_congr rfl (fun i _ => he i)
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          obtain ⟨a, ha, rfl⟩ := hx
          exact ha
        · intro i _ _; exact (hL _ (List.get_mem L i)).1.le
    _ ≤ 1 := hf j

lemma sorted_sortDesc (L : List ℝ) : (sortDesc L).Pairwise (fun a b => b ≤ a) := by
  have := List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
    (fun a b c h1 h2 => by simp at h1 h2 ⊢; linarith)
    (fun a b => by simp; exact le_total b a) L
  exact this.imp (fun h => by simpa using h)

end FFDAux_e3877310

open FFDAux_e3877310 in
open BinPacking.SmallItems in
theorem sol_e3877310 (r d : ℝ) (hr : 1 ≤ r) (hd : 1 ≤ d) (L : List ℝ)
    (hL : IsList L) (h : r * (optBins L : ℝ) + d < (FFD L : ℝ)) :
    r * (optBins (L.filter (fun a => decide ((r - 1) / r < a))) : ℝ) + d <
      (FFD (L.filter (fun a => decide ((r - 1) / r < a))) : ℝ) := by
  have hr0 : 0 < r := by linarith
  set t := (r - 1) / r with ht
  set S := sortDesc L with hSdef
  have hperm : S.Perm L := List.mergeSort_perm _ _
  have hS := sorted_sortDesc L
  have hsplit := split_sorted t S hS
  have hsd : sortDesc (L.filter (fun a => decide (t < a))) = S.filter (fun a => decide (t < a)) := by
    apply List.Perm.eq_of_sortedGE
    · exact List.Pairwise.sortedGE ((sorted_sortDesc _).imp (fun h => h))
    · exact List.Pairwise.sortedGE ((hS.filter _).imp (fun h => h))
    · exact (List.mergeSort_perm _ _).trans (hperm.filter _).symm
  have hFFD : FFD L = ((S.filter (fun a => !decide (t < a))).foldl step
      (ffPack (S.filter (fun a => decide (t < a))))).length := by
    show (ffPack S).length = _
    conv_lhs => rw [hsplit]
    unfold ffPack
    rw [List.foldl_append]
    rfl
  have hFFD' : FFD (L.filter (fun a => decide (t < a))) =
      (ffPack (S.filter (fun a => decide (t < a)))).length := by
    show (ffPack (sortDesc _)).length = _
    rw [hsd]
  have htot : tot ((S.filter (fun a => !decide (t < a))).foldl step
      (ffPack (S.filter (fun a => decide (t < a))))) = L.sum := by
    rw [tot_fold]
    have h0 : tot (ffPack (S.filter (fun a => decide (t < a)))) =
        (S.filter (fun a => decide (t < a))).sum := by
      have := tot_fold (S.filter (fun a => decide (t < a))) []
      rw [show ffPack (S.filter (fun a => decide (t < a))) =
        (S.filter (fun a => decide (t < a))).foldl step [] from rfl, this]
      simp [tot]
    rw [h0, ← List.sum_append, ← hsplit, hperm.sum_eq]
  have hsmall : ∀ a ∈ S.filter (fun a => !decide (t < a)), 0 < a ∧ r * a ≤ r - 1 := by
    intro a ha
    rw [List.mem_filter] at ha
    have hmem : a ∈ L := hperm.mem_iff.mp ha.1
    refine ⟨(hL a hmem).1, ?_⟩
    have hle : a ≤ t := by simpa using ha.2
    rw [ht, le_div_iff₀ hr0] at hle
    linarith
  have hinv := small_phase r hr0 (ffPack (S.filter (fun a => decide (t < a)))).length
    (S.filter (fun a => !decide (t < a))) (ffPack (S.filter (fun a => decide (t < a)))) hsmall
    (Or.inl rfl)
  rw [← hFFD, htot] at hinv
  have hopt := sum_le_optBins L hL
  have hmono := optBins_mono L hL (fun a => decide (t < a))
  rcases hinv with h1 | h1
  · rw [hFFD', ← h1]
    have : (optBins (L.filter (fun a => decide (t < a))) : ℝ) ≤ optBins L := by exact_mod_cast hmono
    nlinarith
  · exfalso
    nlinarith



namespace P6c9b

open BinPacking.SmallItems

theorem w1_eq_of (k : ℕ) (hk : 0 < k) (x : ℝ) (h1 : 1 / ((k : ℝ) + 1) < x) (h2 : x ≤ 1 / (k : ℝ)) :
    w1 x = 1 / (k : ℝ) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : 0 < x := lt_trans (by positivity) h1
  have hfl : ⌊1 / x⌋₊ = k := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · rw [le_div_iff₀ hx]
      rw [le_div_iff₀ hk'] at h2
      linarith
    · rw [div_lt_iff₀ hx]
      rw [div_lt_iff₀ (by linarith)] at h1
      linarith
  unfold w1
  rw [hfl, one_div]

theorem w1_nonneg (y : ℝ) : 0 ≤ w1 y := by
  unfold w1; positivity

theorem w2_cases (k : ℕ) (hk : 0 < k) (x y : ℝ) (h1 : 1 / ((k : ℝ) + 1) < x)
    (h2 : x ≤ 1 / (k : ℝ)) :
    ((k : ℝ) * x + y ≤ 1 ∧ w2 x y = 1 / (k : ℝ) + ((k : ℝ) - 1) / (k : ℝ) * w1 y) ∨
    (1 < (k : ℝ) * x + y ∧ w2 x y = 1 / (k : ℝ) + w1 y) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : 0 < x := lt_trans (by positivity) h1
  have hfl : ⌊1 / x⌋₊ = k := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · rw [le_div_iff₀ hx]
      rw [le_div_iff₀ hk'] at h2
      linarith
    · rw [div_lt_iff₀ hx]
      rw [div_lt_iff₀ (by linarith)] at h1
      linarith
  have hw := w1_eq_of k hk x h1 h2
  by_cases hr : (k : ℝ) * x + y ≤ 1
  · left
    refine ⟨hr, ?_⟩
    unfold w2
    rw [if_pos ⟨by rw [hfl]; exact ⟨h1, h2⟩, by rw [hfl]; exact hr⟩, hfl, hw]
  · right
    refine ⟨lt_of_not_ge hr, ?_⟩
    unfold w2
    rw [if_neg (by rw [hfl]; exact fun h => hr h.2), hw]

theorem piece_cases (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 2) :
    (1 / 3 < x ∧ x ≤ 1 / 2 ∧ w1 x = 1 / 2) ∨ (1 / 4 < x ∧ x ≤ 1 / 3 ∧ w1 x = 1 / 3) ∨
    (1 / 5 < x ∧ x ≤ 1 / 4 ∧ w1 x = 1 / 4) ∨ (1 / 6 < x ∧ x ≤ 1 / 5 ∧ w1 x = 1 / 5) ∨
    (1 / 7 < x ∧ x ≤ 1 / 6 ∧ w1 x = 1 / 6) := by
  rcases lt_or_ge (1 / 3) x with h3 | h3
  · exact Or.inl ⟨h3, h2, by
      have := w1_eq_of 2 (by norm_num) x (by norm_num; linarith) (by norm_num; linarith)
      simpa using this⟩
  rcases lt_or_ge (1 / 4) x with h4 | h4
  · exact Or.inr <| Or.inl ⟨h4, h3, by
      have := w1_eq_of 3 (by norm_num) x (by norm_num; linarith) (by norm_num; linarith)
      simpa using this⟩
  rcases lt_or_ge (1 / 5) x with h5 | h5
  · exact Or.inr <| Or.inr <| Or.inl ⟨h5, h4, by
      have := w1_eq_of 4 (by norm_num) x (by norm_num; linarith) (by norm_num; linarith)
      simpa using this⟩
  rcases lt_or_ge (1 / 6) x with h6 | h6
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨h6, h5, by
      have := w1_eq_of 5 (by norm_num) x (by norm_num; linarith) (by norm_num; linarith)
      simpa using this⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨h1, h6, by
      have := w1_eq_of 6 (by norm_num) x (by norm_num; linarith) (by norm_num; linarith)
      simpa using this⟩

theorem pc2 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 2) :
    (1 / 3 < x ∧ x ≤ 1 / 2 ∧ w1 x = 1 / 2) ∨ (1 / 4 < x ∧ x ≤ 1 / 3 ∧ w1 x = 1 / 3) ∨
    (1 / 5 < x ∧ x ≤ 1 / 4 ∧ w1 x = 1 / 4) ∨ (1 / 6 < x ∧ x ≤ 1 / 5 ∧ w1 x = 1 / 5) ∨
    (1 / 7 < x ∧ x ≤ 1 / 6 ∧ w1 x = 1 / 6) := piece_cases x h1 h2

theorem pc3 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 3) :
    (1 / 4 < x ∧ x ≤ 1 / 3 ∧ w1 x = 1 / 3) ∨
    (1 / 5 < x ∧ x ≤ 1 / 4 ∧ w1 x = 1 / 4) ∨ (1 / 6 < x ∧ x ≤ 1 / 5 ∧ w1 x = 1 / 5) ∨
    (1 / 7 < x ∧ x ≤ 1 / 6 ∧ w1 x = 1 / 6) := by
  rcases piece_cases x h1 (by linarith) with h | h
  · exfalso; linarith [h.1]
  · exact h

theorem pc4 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 4) :
    (1 / 5 < x ∧ x ≤ 1 / 4 ∧ w1 x = 1 / 4) ∨ (1 / 6 < x ∧ x ≤ 1 / 5 ∧ w1 x = 1 / 5) ∨
    (1 / 7 < x ∧ x ≤ 1 / 6 ∧ w1 x = 1 / 6) := by
  rcases pc3 x h1 (by linarith) with h | h
  · exfalso; linarith [h.1]
  · exact h

theorem pc5 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 5) :
    (1 / 6 < x ∧ x ≤ 1 / 5 ∧ w1 x = 1 / 5) ∨ (1 / 7 < x ∧ x ≤ 1 / 6 ∧ w1 x = 1 / 6) := by
  rcases pc4 x h1 (by linarith) with h | h
  · exfalso; linarith [h.1]
  · exact h

theorem pc6 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 6) :
    (1 / 7 < x ∧ x ≤ 1 / 6 ∧ w1 x = 1 / 6) := by
  rcases pc5 x h1 (by linarith) with h | h
  · exfalso; linarith [h.1]
  · exact h

theorem w1le2 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 2) : w1 x ≤ 1 / 2 := by
  rcases pc2 x h1 h2 with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> norm_num

theorem w1le3 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 3) : w1 x ≤ 1 / 3 := by
  rcases pc3 x h1 h2 with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> norm_num

theorem w1le4 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 4) : w1 x ≤ 1 / 4 := by
  rcases pc4 x h1 h2 with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> norm_num

theorem w1le5 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 5) : w1 x ≤ 1 / 5 := by
  rcases pc5 x h1 h2 with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> norm_num

theorem w1le6 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 6) : w1 x ≤ 1 / 6 := by
  rcases pc6 x h1 h2 with ⟨-, -, h⟩ <;> rw [h] <;> norm_num

theorem w2c2 (x y : ℝ) (h1 : 1 / 3 < x) (h2 : x ≤ 1 / 2) :
    (2 * x + y ≤ 1 ∧ w2 x y = 1 / 2 + 1 / 2 * w1 y) ∨ (1 < 2 * x + y ∧ w2 x y = 1 / 2 + w1 y) := by
  have := w2_cases 2 (by norm_num) x y (by norm_num; linarith) (by norm_num; linarith)
  norm_num at this ⊢; exact this

theorem w2c3 (x y : ℝ) (h1 : 1 / 4 < x) (h2 : x ≤ 1 / 3) :
    (3 * x + y ≤ 1 ∧ w2 x y = 1 / 3 + 2 / 3 * w1 y) ∨ (1 < 3 * x + y ∧ w2 x y = 1 / 3 + w1 y) := by
  have := w2_cases 3 (by norm_num) x y (by norm_num; linarith) (by norm_num; linarith)
  norm_num at this ⊢; exact this

theorem w2c4 (x y : ℝ) (h1 : 1 / 5 < x) (h2 : x ≤ 1 / 4) :
    (4 * x + y ≤ 1 ∧ w2 x y = 1 / 4 + 3 / 4 * w1 y) ∨ (1 < 4 * x + y ∧ w2 x y = 1 / 4 + w1 y) := by
  have := w2_cases 4 (by norm_num) x y (by norm_num; linarith) (by norm_num; linarith)
  norm_num at this ⊢; exact this

theorem w2c5 (x y : ℝ) (h1 : 1 / 6 < x) (h2 : x ≤ 1 / 5) :
    (5 * x + y ≤ 1 ∧ w2 x y = 1 / 5 + 4 / 5 * w1 y) ∨ (1 < 5 * x + y ∧ w2 x y = 1 / 5 + w1 y) := by
  have := w2_cases 5 (by norm_num) x y (by norm_num; linarith) (by norm_num; linarith)
  norm_num at this ⊢; exact this

theorem w2c6 (x y : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 6) :
    (6 * x + y ≤ 1 ∧ w2 x y = 1 / 6 + 5 / 6 * w1 y) ∨ (1 < 6 * x + y ∧ w2 x y = 1 / 6 + w1 y) := by
  have := w2_cases 6 (by norm_num) x y (by norm_num; linarith) (by norm_num; linarith)
  norm_num at this ⊢; exact this

/-! ### w12 for the identity, one swap, two disjoint swaps -/

theorem one_mem_pairings (n : ℕ) : (1 : Equiv.Perm (Fin n)) ∈ pairings n := by
  simp [pairings]

theorem swap_mem_pairings {n : ℕ} (i j : Fin n) : Equiv.swap i j ∈ pairings n := by
  simp [pairings, Equiv.swap_mul_self]

theorem swap_comm_of_ne {n : ℕ} (i j k l : Fin n) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) : Equiv.swap i j * Equiv.swap k l = Equiv.swap k l * Equiv.swap i j := by
  apply Equiv.ext; intro x
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  by_cases h1 : x = i
  · subst h1
    rw [Equiv.swap_apply_of_ne_of_ne hik hil, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hjk hjl]
  by_cases h2 : x = j
  · subst h2
    rw [Equiv.swap_apply_of_ne_of_ne hjk hjl, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hik hil]
  by_cases h3 : x = k
  · subst h3
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk),
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hil) (Ne.symm hjl), Equiv.swap_apply_left]
  by_cases h4 : x = l
  · subst h4
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm hil) (Ne.symm hjl),
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk), Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne h3 h4, Equiv.swap_apply_of_ne_of_ne h1 h2,
    Equiv.swap_apply_of_ne_of_ne h3 h4]

theorem swap2_mem_pairings {n : ℕ} (i j k l : Fin n) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) : Equiv.swap i j * Equiv.swap k l ∈ pairings n := by
  simp only [pairings, Finset.mem_filter, Finset.mem_univ, true_and]
  have hc := swap_comm_of_ne i j k l hik hil hjk hjl
  calc Equiv.swap i j * Equiv.swap k l * (Equiv.swap i j * Equiv.swap k l)
      = Equiv.swap i j * (Equiv.swap k l * Equiv.swap i j) * Equiv.swap k l := by
        simp only [mul_assoc]
    _ = 1 := by
        rw [← hc]
        simp only [Equiv.swap_mul_self_mul, Equiv.swap_mul_self]

theorem sum_w1 (S : List ℝ) : ∑ t : Fin S.length, w1 (S.get t) = (S.map w1).sum := by
  simp

theorem w12_one (S : List ℝ) : w12 S 1 = ∑ i : Fin S.length, w1 (S.get i) := by
  unfold w12
  simp

theorem w12_swap (S : List ℝ) (i j : Fin S.length) (hij : i < j) :
    w12 S (Equiv.swap i j) = (∑ t : Fin S.length, w1 (S.get t)) - w1 (S.get i) - w1 (S.get j)
      + w2 (S.get i) (S.get j) := by
  unfold w12
  have hne : i ≠ j := ne_of_lt hij
  have e1 : (Finset.univ.filter (fun t => Equiv.swap i j t = t)) = (Finset.univ.erase i).erase j := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq]
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all [eq_comm]
  have e2 : (Finset.univ.filter (fun t => t < Equiv.swap i j t)) = {i} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all [lt_asymm]
  rw [e1, e2, Finset.sum_singleton, Equiv.swap_apply_left]
  rw [Finset.sum_erase_eq_sub (by simp [Ne.symm hne]), Finset.sum_erase_eq_sub (by simp)]

theorem w12_swap2 (S : List ℝ) (i j k l : Fin S.length) (hij : i < j) (hkl : k < l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    w12 S (Equiv.swap i j * Equiv.swap k l) = (∑ t : Fin S.length, w1 (S.get t))
      - w1 (S.get i) - w1 (S.get j) - w1 (S.get k) - w1 (S.get l)
      + w2 (S.get i) (S.get j) + w2 (S.get k) (S.get l) := by
  unfold w12
  have hne : i ≠ j := ne_of_lt hij
  have hne' : k ≠ l := ne_of_lt hkl
  have vi : (Equiv.swap i j * Equiv.swap k l) i = j := by
    simp [Equiv.swap_apply_of_ne_of_ne hik hil]
  have vj : (Equiv.swap i j * Equiv.swap k l) j = i := by
    simp [Equiv.swap_apply_of_ne_of_ne hjk hjl]
  have vk : (Equiv.swap i j * Equiv.swap k l) k = l := by
    simp [Equiv.swap_apply_of_ne_of_ne (Ne.symm hil) (Ne.symm hjl)]
  have vl : (Equiv.swap i j * Equiv.swap k l) l = k := by
    simp [Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)]
  have vo : ∀ t, t ≠ i → t ≠ j → t ≠ k → t ≠ l → (Equiv.swap i j * Equiv.swap k l) t = t := by
    intro t h1 h2 h3 h4
    simp [Equiv.swap_apply_of_ne_of_ne h3 h4, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have e1 : (Finset.univ.filter (fun t => (Equiv.swap i j * Equiv.swap k l) t = t))
      = (((Finset.univ.erase i).erase j).erase k).erase l := by
    ext t
    rw [Finset.mem_filter]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, true_and, ne_eq]
    by_cases h1 : t = i
    · rw [h1, vi]; simp [Ne.symm hne]
    by_cases h2 : t = j
    · rw [h2, vj]; simp [hne]
    by_cases h3 : t = k
    · rw [h3, vk]; simp [Ne.symm hne']
    by_cases h4 : t = l
    · rw [h4, vl]; simp [hne']
    rw [vo t h1 h2 h3 h4]; simp [h1, h2, h3, h4]
  have e2 : (Finset.univ.filter (fun t => t < (Equiv.swap i j * Equiv.swap k l) t)) = {i, k} := by
    ext t
    rw [Finset.mem_filter]
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, true_and]
    by_cases h1 : t = i
    · rw [h1, vi]; simp [hij]
    by_cases h2 : t = j
    · rw [h2, vj]; simp [not_lt.mpr hij.le, hne, Ne.symm hne, hjk]
    by_cases h3 : t = k
    · rw [h3, vk]; simp [hkl]
    by_cases h4 : t = l
    · rw [h4, vl]; simp [not_lt.mpr hkl.le, Ne.symm hil, Ne.symm hne']
    rw [vo t h1 h2 h3 h4]; simp [h1, h3]
  rw [e1, e2, Finset.sum_pair hik, vi, vk]
  rw [Finset.sum_erase_eq_sub (by simp [Ne.symm hil, Ne.symm hjl, Ne.symm hne']),
    Finset.sum_erase_eq_sub (by simp [Ne.symm hik, Ne.symm hjk]),
    Finset.sum_erase_eq_sub (by simp [Ne.symm hne]), Finset.sum_erase_eq_sub (by simp)]
  ring

set_option maxHeartbeats 4000000 in
theorem core1 (x0 : ℝ) (l0 : 1 / 7 < x0) (u0 : x0 ≤ 1 / 2)  (hs : x0 ≤ 1) :
    ∃ σ ∈ pairings [x0].length, w12 [x0] σ ≤ 71 / 60 := by
  exact ⟨1, one_mem_pairings _, by
    rw [w12_one, sum_w1]; show (w1 x0 + 0) ≤ 71 / 60
    have c0 := w1le2 x0 l0 (by linarith only [u0])
    linarith only [c0]⟩

set_option maxHeartbeats 4000000 in
theorem core2 (x0 x1 : ℝ) (l0 : 1 / 7 < x0) (l1 : 1 / 7 < x1) (u0 : x0 ≤ 1 / 2) (o0 : x1 ≤ x0) (hs : x0 + x1 ≤ 1) :
    ∃ σ ∈ pairings [x0, x1].length, w12 [x0, x1] σ ≤ 71 / 60 := by
  exact ⟨1, one_mem_pairings _, by
    rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + 0)) ≤ 71 / 60
    have c0 := w1le2 x0 l0 (by linarith only [u0])
    have c1 := w1le2 x1 l1 (by linarith only [u0, o0])
    linarith only [c0, c1]⟩

set_option maxHeartbeats 4000000 in
theorem core3 (x0 x1 x2 : ℝ) (l0 : 1 / 7 < x0) (l1 : 1 / 7 < x1) (l2 : 1 / 7 < x2) (u0 : x0 ≤ 1 / 2) (o0 : x1 ≤ x0) (o1 : x2 ≤ x1) (hs : x0 + x1 + x2 ≤ 1) :
    ∃ σ ∈ pairings [x0, x1, x2].length, w12 [x0, x1, x2] σ ≤ 71 / 60 := by
  rcases pc2 x0 l0 u0 with ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩
  · rcases pc2 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc2 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · exfalso; linarith only [a2, o0, o1, hs]
      · refine ⟨Equiv.swap ⟨1, (show 1 < 3 by decide)⟩ ⟨2, (show 2 < 3 by decide)⟩, swap_mem_pairings _ _, ?_⟩
        rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 1 < 2 by decide)), sum_w1]
        show (w1 x0 + (w1 x1 + (w1 x2 + 0))) - w1 x1 - w1 x2 + w2 x1 x2 ≤ 71 / 60
        rcases w2c2 x1 x2 a1 b1 with ⟨r1, e1⟩ | ⟨r1, e1⟩
        · norm_num [e1, q0, q1, q2]
        · exfalso; linarith only [o0, hs, r1]
      · refine ⟨Equiv.swap ⟨1, (show 1 < 3 by decide)⟩ ⟨2, (show 2 < 3 by decide)⟩, swap_mem_pairings _ _, ?_⟩
        rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 1 < 2 by decide)), sum_w1]
        show (w1 x0 + (w1 x1 + (w1 x2 + 0))) - w1 x1 - w1 x2 + w2 x1 x2 ≤ 71 / 60
        rcases w2c2 x1 x2 a1 b1 with ⟨r1, e1⟩ | ⟨r1, e1⟩
        · norm_num [e1, q0, q1, q2]
        · exfalso; linarith only [o0, hs, r1]
      · refine ⟨Equiv.swap ⟨1, (show 1 < 3 by decide)⟩ ⟨2, (show 2 < 3 by decide)⟩, swap_mem_pairings _ _, ?_⟩
        rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 1 < 2 by decide)), sum_w1]
        show (w1 x0 + (w1 x1 + (w1 x2 + 0))) - w1 x1 - w1 x2 + w2 x1 x2 ≤ 71 / 60
        rcases w2c2 x1 x2 a1 b1 with ⟨r1, e1⟩ | ⟨r1, e1⟩
        · norm_num [e1, q0, q1, q2]
        · exfalso; linarith only [o0, hs, r1]
      · exact ⟨1, one_mem_pairings _, by rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60; norm_num [q0, q1, q2]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
        have c2 := w1le3 x2 l2 (by linarith only [b1, o1])
        linarith only [q0, q1, c2]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
        have c2 := w1le4 x2 l2 (by linarith only [b1, o1])
        linarith only [q0, q1, c2]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
        have c2 := w1le5 x2 l2 (by linarith only [b1, o1])
        linarith only [q0, q1, c2]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        linarith only [q0, q1, c2]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
      have c1 := w1le3 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le3 x2 l2 (by linarith only [b0, o0, o1])
      linarith only [q0, c1, c2]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
      have c1 := w1le4 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le4 x2 l2 (by linarith only [b0, o0, o1])
      linarith only [q0, c1, c2]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
      have c1 := w1le5 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le5 x2 l2 (by linarith only [b0, o0, o1])
      linarith only [q0, c1, c2]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
      have c1 := w1le6 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le6 x2 l2 (by linarith only [b0, o0, o1])
      linarith only [q0, c1, c2]⟩

set_option maxHeartbeats 4000000 in
theorem core4 (x0 x1 x2 x3 : ℝ) (l0 : 1 / 7 < x0) (l1 : 1 / 7 < x1) (l2 : 1 / 7 < x2) (l3 : 1 / 7 < x3) (u0 : x0 ≤ 1 / 2) (o0 : x1 ≤ x0) (o1 : x2 ≤ x1) (o2 : x3 ≤ x2) (hs : x0 + x1 + x2 + x3 ≤ 1) :
    ∃ σ ∈ pairings [x0, x1, x2, x3].length, w12 [x0, x1, x2, x3] σ ≤ 71 / 60 := by
  rcases pc2 x0 l0 u0 with ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩
  · rcases pc2 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc2 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · exfalso; linarith only [a2, l3, o0, o1, hs]
      · exfalso; linarith only [a1, a2, l3, o0, hs]
      · exfalso; linarith only [a1, a2, l3, o0, hs]
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · exfalso; linarith only [a1, a3, o0, o2, hs]
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨2, (show 2 < 4 by decide)⟩ * Equiv.swap ⟨1, (show 1 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap2_mem_pairings _ _ _ _ (Fin.ne_of_val_ne (show 0 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 3 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 3 by decide)), ?_⟩
          rw [w12_swap2 _ _ _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 2 by decide)) (Fin.mk_lt_mk.mpr (show 1 < 3 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 3 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 3 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x2 - w1 x1 - w1 x3 + w2 x0 x2 + w2 x1 x3 ≤ 71 / 60
          rcases w2c2 x0 x2 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · rcases w2c2 x1 x3 a1 b1 with ⟨r2, e2⟩ | ⟨r2, e2⟩
            · norm_num [e1, e2, q0, q1, q2, q3]
            · exfalso; linarith only [o0, o2, r1, r2]
          · rcases w2c2 x1 x3 a1 b1 with ⟨r2, e2⟩ | ⟨r2, e2⟩
            · exfalso; linarith only [a1, a3, o2, hs, r1]
            · exfalso; linarith only [a3, o2, hs, r1, r2]
      · rcases pc6 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨2, (show 2 < 4 by decide)⟩ * Equiv.swap ⟨1, (show 1 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap2_mem_pairings _ _ _ _ (Fin.ne_of_val_ne (show 0 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 3 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 3 by decide)), ?_⟩
          rw [w12_swap2 _ _ _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 2 by decide)) (Fin.mk_lt_mk.mpr (show 1 < 3 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 3 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 3 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x2 - w1 x1 - w1 x3 + w2 x0 x2 + w2 x1 x3 ≤ 71 / 60
          rcases w2c2 x0 x2 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · rcases w2c2 x1 x3 a1 b1 with ⟨r2, e2⟩ | ⟨r2, e2⟩
            · norm_num [e1, e2, q0, q1, q2, q3]
            · exfalso; linarith only [o0, o2, r1, r2]
          · rcases w2c2 x1 x3 a1 b1 with ⟨r2, e2⟩ | ⟨r2, e2⟩
            · exfalso; linarith only [a1, a3, o2, hs, r1]
            · exfalso; linarith only [a3, o2, hs, r1, r2]
    · rcases pc3 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc3 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · exfalso; linarith only [a3, o0, o1, o2, hs]
        · exfalso; linarith only [a0, a2, a3, o1, hs]
        · exfalso; linarith only [a0, a2, a3, o1, hs]
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨1, (show 1 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
          rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [a2, a3, o1, hs, r1]
      · rcases pc4 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨1, (show 1 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
          rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [a3, o1, o2, hs, r1]
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨2, (show 2 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 2 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x2 + w2 x0 x2 ≤ 71 / 60
          rcases w2c2 x0 x2 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [a1, a3, o2, hs, r1]
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 3 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x3 + w2 x0 x3 ≤ 71 / 60
          rcases w2c2 x0 x3 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [a1, a2, a3, hs, r1]
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨2, (show 2 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 2 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x2 + w2 x0 x2 ≤ 71 / 60
          rcases w2c2 x0 x2 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [a1, a3, o2, hs, r1]
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨2, (show 2 < 4 by decide)⟩ * Equiv.swap ⟨1, (show 1 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap2_mem_pairings _ _ _ _ (Fin.ne_of_val_ne (show 0 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 3 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 3 by decide)), ?_⟩
          rw [w12_swap2 _ _ _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 2 by decide)) (Fin.mk_lt_mk.mpr (show 1 < 3 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 3 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 3 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x2 - w1 x1 - w1 x3 + w2 x0 x2 + w2 x1 x3 ≤ 71 / 60
          rcases w2c2 x0 x2 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · rcases w2c3 x1 x3 a1 b1 with ⟨r2, e2⟩ | ⟨r2, e2⟩
            · norm_num [e1, e2, q0, q1, q2, q3]
            · norm_num [e1, e2, q0, q1, q2, q3]
          · rcases w2c3 x1 x3 a1 b1 with ⟨r2, e2⟩ | ⟨r2, e2⟩
            · norm_num [e1, e2, q0, q1, q2, q3]
            · exfalso; linarith only [a3, o2, hs, r1, r2]
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          linarith only [q0, q1, q2, c3]⟩
    · rcases pc4 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc4 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨1, (show 1 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
          rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [a3, o1, o2, hs, r1]
        · by_cases hsp : 2 * x0 + x3 ≤ 1
          · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 3 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x3 + w2 x0 x3 ≤ 71 / 60
            rcases w2c2 x0 x3 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3]
            · exfalso; linarith only [r1, hsp]
          · refine ⟨Equiv.swap ⟨2, (show 2 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 2 < 3 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x2 - w1 x3 + w2 x2 x3 ≤ 71 / 60
            rcases w2c4 x2 x3 a2 b2 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3]
            · exfalso; linarith only [o1, hs, r1, hsp]
        · exact ⟨1, one_mem_pairings _, by rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60; norm_num [q0, q1, q2, q3]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
          have c3 := w1le5 x3 l3 (by linarith only [b2, o2])
          linarith only [q0, q1, q2, c3]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          linarith only [q0, q1, q2, c3]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
        have c2 := w1le5 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le5 x3 l3 (by linarith only [b1, o1, o2])
        linarith only [q0, q1, c2, c3]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        linarith only [q0, q1, c2, c3]⟩
  · rcases pc3 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc3 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc3 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · exfalso; linarith only [a3, o0, o1, o2, hs]
        · refine ⟨Equiv.swap ⟨2, (show 2 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 2 < 3 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x2 - w1 x3 + w2 x2 x3 ≤ 71 / 60
          rcases w2c3 x2 x3 a2 b2 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [o0, o1, hs, r1]
        · refine ⟨Equiv.swap ⟨2, (show 2 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 2 < 3 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x2 - w1 x3 + w2 x2 x3 ≤ 71 / 60
          rcases w2c3 x2 x3 a2 b2 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [o0, o1, hs, r1]
        · exact ⟨1, one_mem_pairings _, by rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60; norm_num [q0, q1, q2, q3]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
          have c3 := w1le4 x3 l3 (by linarith only [b2, o2])
          linarith only [q0, q1, q2, c3]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
          have c3 := w1le5 x3 l3 (by linarith only [b2, o2])
          linarith only [q0, q1, q2, c3]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          linarith only [q0, q1, q2, c3]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
        have c2 := w1le4 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le4 x3 l3 (by linarith only [b1, o1, o2])
        linarith only [q0, q1, c2, c3]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
        have c2 := w1le5 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le5 x3 l3 (by linarith only [b1, o1, o2])
        linarith only [q0, q1, c2, c3]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        linarith only [q0, q1, c2, c3]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
      have c1 := w1le4 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le4 x2 l2 (by linarith only [b0, o0, o1])
      have c3 := w1le4 x3 l3 (by linarith only [b0, o0, o1, o2])
      linarith only [q0, c1, c2, c3]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
      have c1 := w1le5 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le5 x2 l2 (by linarith only [b0, o0, o1])
      have c3 := w1le5 x3 l3 (by linarith only [b0, o0, o1, o2])
      linarith only [q0, c1, c2, c3]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
      have c1 := w1le6 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le6 x2 l2 (by linarith only [b0, o0, o1])
      have c3 := w1le6 x3 l3 (by linarith only [b0, o0, o1, o2])
      linarith only [q0, c1, c2, c3]⟩

set_option maxHeartbeats 4000000 in
theorem core5 (x0 x1 x2 x3 x4 : ℝ) (l0 : 1 / 7 < x0) (l1 : 1 / 7 < x1) (l2 : 1 / 7 < x2) (l3 : 1 / 7 < x3) (l4 : 1 / 7 < x4) (u0 : x0 ≤ 1 / 2) (o0 : x1 ≤ x0) (o1 : x2 ≤ x1) (o2 : x3 ≤ x2) (o3 : x4 ≤ x3) (hs : x0 + x1 + x2 + x3 + x4 ≤ 1) :
    ∃ σ ∈ pairings [x0, x1, x2, x3, x4].length, w12 [x0, x1, x2, x3, x4] σ ≤ 71 / 60 := by
  rcases pc2 x0 l0 u0 with ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩
  · rcases pc2 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · exfalso; linarith only [a1, l4, o0, o2, o3, hs]
    · exfalso; linarith only [a0, a1, l4, o2, o3, hs]
    · rcases pc4 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · exfalso; linarith only [a0, a2, l4, o1, o3, hs]
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · exfalso; linarith only [a0, a1, a3, l4, o2, hs]
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
            rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o1, o2, o3, hs, r1]
      · rcases pc6 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
            rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o1, o2, o3, hs, r1]
    · rcases pc5 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · rcases pc5 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · exfalso; linarith only [a0, a4, o1, o2, o3, hs]
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
            rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o1, o2, o3, hs, r1]
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
            rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o1, o2, o3, hs, r1]
      · rcases pc6 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
            rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o1, o2, o3, hs, r1]
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le6 x4 l4 (by linarith only [b1, o1, o2, o3])
        linarith only [q0, q1, c2, c3, c4]⟩
  · rcases pc3 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc3 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · exfalso; linarith only [a2, l4, o0, o1, o3, hs]
      · rcases pc4 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · exfalso; linarith only [a1, a3, l4, o0, o2, hs]
        · exfalso; linarith only [a1, a2, a3, l4, o0, hs]
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨1, (show 1 < 5 by decide)⟩ ⟨2, (show 2 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 1 < 2 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x1 - w1 x2 + w2 x1 x2 ≤ 71 / 60
            rcases w2c3 x1 x2 a1 b1 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o0, o2, o3, hs, r1]
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · rcases pc5 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · exfalso; linarith only [a1, a4, o0, o2, o3, hs]
          · refine ⟨Equiv.swap ⟨1, (show 1 < 5 by decide)⟩ ⟨2, (show 2 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 1 < 2 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x1 - w1 x2 + w2 x1 x2 ≤ 71 / 60
            rcases w2c3 x1 x2 a1 b1 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o0, o2, o3, hs, r1]
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨1, (show 1 < 5 by decide)⟩ ⟨2, (show 2 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 1 < 2 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x1 - w1 x2 + w2 x1 x2 ≤ 71 / 60
            rcases w2c3 x1 x2 a1 b1 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o0, o2, o3, hs, r1]
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le6 x4 l4 (by linarith only [b2, o2, o3])
          linarith only [q0, q1, q2, c3, c4]⟩
    · rcases pc4 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc4 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · rcases pc4 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · exfalso; linarith only [a4, o0, o1, o2, o3, hs]
          · exfalso; linarith only [a0, a3, a4, o1, o2, hs]
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
            rcases w2c3 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a3, a4, o1, o2, hs, r1]
        · rcases pc5 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨2, (show 2 < 5 by decide)⟩ ⟨3, (show 3 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 2 < 3 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x2 - w1 x3 + w2 x2 x3 ≤ 71 / 60
            rcases w2c4 x2 x3 a2 b2 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a0, a4, o1, o3, hs, r1]
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩ * Equiv.swap ⟨2, (show 2 < 5 by decide)⟩ ⟨4, (show 4 < 5 by decide)⟩, swap2_mem_pairings _ _ _ _ (Fin.ne_of_val_ne (show 0 ≠ 2 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 4 by decide)) (Fin.ne_of_val_ne (show 1 ≠ 2 by decide)) (Fin.ne_of_val_ne (show 1 ≠ 4 by decide)), ?_⟩
            rw [w12_swap2 _ _ _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)) (Fin.mk_lt_mk.mpr (show 2 < 4 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 2 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 4 by decide)) (Fin.ne_of_val_ne (show 1 ≠ 2 by decide)) (Fin.ne_of_val_ne (show 1 ≠ 4 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 - w1 x2 - w1 x4 + w2 x0 x1 + w2 x2 x4 ≤ 71 / 60
            rcases w2c3 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · rcases w2c4 x2 x4 a2 b2 with ⟨r2, e2⟩ | ⟨r2, e2⟩
              · norm_num [e1, e2, q0, q1, q2, q3, q4]
              · norm_num [e1, e2, q0, q1, q2, q3, q4]
            · rcases w2c4 x2 x4 a2 b2 with ⟨r2, e2⟩ | ⟨r2, e2⟩
              · norm_num [e1, e2, q0, q1, q2, q3, q4]
              · exfalso; linarith only [a3, a4, o1, hs, r1, r2]
        · exact ⟨1, one_mem_pairings _, by
            rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
            have c4 := w1le6 x4 l4 (by linarith only [b3, o3])
            linarith only [q0, q1, q2, q3, c4]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
          have c3 := w1le5 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le5 x4 l4 (by linarith only [b2, o2, o3])
          linarith only [q0, q1, q2, c3, c4]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le6 x4 l4 (by linarith only [b2, o2, o3])
          linarith only [q0, q1, q2, c3, c4]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
        have c2 := w1le5 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le5 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le5 x4 l4 (by linarith only [b1, o1, o2, o3])
        linarith only [q0, q1, c2, c3, c4]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le6 x4 l4 (by linarith only [b1, o1, o2, o3])
        linarith only [q0, q1, c2, c3, c4]⟩
  · rcases pc4 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc4 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc4 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · rcases pc4 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · exfalso; linarith only [a4, o0, o1, o2, o3, hs]
          · refine ⟨Equiv.swap ⟨3, (show 3 < 5 by decide)⟩ ⟨4, (show 4 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 3 < 4 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x3 - w1 x4 + w2 x3 x4 ≤ 71 / 60
            rcases w2c4 x3 x4 a3 b3 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [o0, o1, o2, hs, r1]
          · exact ⟨1, one_mem_pairings _, by rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60; norm_num [q0, q1, q2, q3, q4]⟩
        · exact ⟨1, one_mem_pairings _, by
            rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
            have c4 := w1le5 x4 l4 (by linarith only [b3, o3])
            linarith only [q0, q1, q2, q3, c4]⟩
        · exact ⟨1, one_mem_pairings _, by
            rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
            have c4 := w1le6 x4 l4 (by linarith only [b3, o3])
            linarith only [q0, q1, q2, q3, c4]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
          have c3 := w1le5 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le5 x4 l4 (by linarith only [b2, o2, o3])
          linarith only [q0, q1, q2, c3, c4]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le6 x4 l4 (by linarith only [b2, o2, o3])
          linarith only [q0, q1, q2, c3, c4]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
        have c2 := w1le5 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le5 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le5 x4 l4 (by linarith only [b1, o1, o2, o3])
        linarith only [q0, q1, c2, c3, c4]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le6 x4 l4 (by linarith only [b1, o1, o2, o3])
        linarith only [q0, q1, c2, c3, c4]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
      have c1 := w1le5 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le5 x2 l2 (by linarith only [b0, o0, o1])
      have c3 := w1le5 x3 l3 (by linarith only [b0, o0, o1, o2])
      have c4 := w1le5 x4 l4 (by linarith only [b0, o0, o1, o2, o3])
      linarith only [q0, c1, c2, c3, c4]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
      have c1 := w1le6 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le6 x2 l2 (by linarith only [b0, o0, o1])
      have c3 := w1le6 x3 l3 (by linarith only [b0, o0, o1, o2])
      have c4 := w1le6 x4 l4 (by linarith only [b0, o0, o1, o2, o3])
      linarith only [q0, c1, c2, c3, c4]⟩

set_option maxHeartbeats 4000000 in
theorem core6 (x0 x1 x2 x3 x4 x5 : ℝ) (l0 : 1 / 7 < x0) (l1 : 1 / 7 < x1) (l2 : 1 / 7 < x2) (l3 : 1 / 7 < x3) (l4 : 1 / 7 < x4) (l5 : 1 / 7 < x5) (u0 : x0 ≤ 1 / 2) (o0 : x1 ≤ x0) (o1 : x2 ≤ x1) (o2 : x3 ≤ x2) (o3 : x4 ≤ x3) (o4 : x5 ≤ x4) (hs : x0 + x1 + x2 + x3 + x4 + x5 ≤ 1) :
    ∃ σ ∈ pairings [x0, x1, x2, x3, x4, x5].length, w12 [x0, x1, x2, x3, x4, x5] σ ≤ 71 / 60 := by
  rcases pc2 x0 l0 u0 with ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩
  · exfalso; linarith only [a0, l5, o1, o2, o3, o4, hs]
  · rcases pc3 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · exfalso; linarith only [a1, l5, o0, o2, o3, o4, hs]
    · exfalso; linarith only [a0, a1, l5, o2, o3, o4, hs]
    · rcases pc5 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · exfalso; linarith only [a0, a2, l5, o1, o3, o4, hs]
      · rcases pc6 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · rcases pc6 x5 l5 (le_trans o4 b4) with ⟨a5, b5, q5⟩
            · refine ⟨Equiv.swap ⟨0, (show 0 < 6 by decide)⟩ ⟨1, (show 1 < 6 by decide)⟩, swap_mem_pairings _ _, ?_⟩
              rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
              show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
              rcases w2c3 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
              · norm_num [e1, q0, q1, q2, q3, q4, q5]
              · exfalso; linarith only [a5, o1, o2, o3, o4, hs, r1]
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le6 x4 l4 (by linarith only [b1, o1, o2, o3])
        have c5 := w1le6 x5 l5 (by linarith only [b1, o1, o2, o3, o4])
        linarith only [q0, q1, c2, c3, c4, c5]⟩
  · rcases pc4 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc4 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · exfalso; linarith only [a2, l5, o0, o1, o3, o4, hs]
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · exfalso; linarith only [a1, a3, l5, o0, o2, o4, hs]
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · rcases pc6 x5 l5 (le_trans o4 b4) with ⟨a5, b5, q5⟩
            · refine ⟨Equiv.swap ⟨2, (show 2 < 6 by decide)⟩ ⟨3, (show 3 < 6 by decide)⟩, swap_mem_pairings _ _, ?_⟩
              rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 2 < 3 by decide)), sum_w1]
              show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) - w1 x2 - w1 x3 + w2 x2 x3 ≤ 71 / 60
              rcases w2c5 x2 x3 a2 b2 with ⟨r1, e1⟩ | ⟨r1, e1⟩
              · norm_num [e1, q0, q1, q2, q3, q4, q5]
              · exfalso; linarith only [a1, a5, o0, o3, o4, hs, r1]
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le6 x4 l4 (by linarith only [b2, o2, o3])
          have c5 := w1le6 x5 l5 (by linarith only [b2, o2, o3, o4])
          linarith only [q0, q1, q2, c3, c4, c5]⟩
    · rcases pc5 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · rcases pc5 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · exfalso; linarith only [a0, a4, l5, o1, o2, o3, hs]
          · exact ⟨1, one_mem_pairings _, by
              rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
              have c5 := w1le6 x5 l5 (by linarith only [b4, o4])
              linarith only [q0, q1, q2, q3, q4, c5]⟩
        · exact ⟨1, one_mem_pairings _, by
            rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
            have c4 := w1le6 x4 l4 (by linarith only [b3, o3])
            have c5 := w1le6 x5 l5 (by linarith only [b3, o3, o4])
            linarith only [q0, q1, q2, q3, c4, c5]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le6 x4 l4 (by linarith only [b2, o2, o3])
          have c5 := w1le6 x5 l5 (by linarith only [b2, o2, o3, o4])
          linarith only [q0, q1, q2, c3, c4, c5]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le6 x4 l4 (by linarith only [b1, o1, o2, o3])
        have c5 := w1le6 x5 l5 (by linarith only [b1, o1, o2, o3, o4])
        linarith only [q0, q1, c2, c3, c4, c5]⟩
  · rcases pc5 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc5 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · rcases pc5 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · rcases pc5 x5 l5 (le_trans o4 b4) with ⟨a5, b5, q5⟩ | ⟨a5, b5, q5⟩
            · exfalso; linarith only [a5, o0, o1, o2, o3, o4, hs]
            · exact ⟨1, one_mem_pairings _, by rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60; norm_num [q0, q1, q2, q3, q4, q5]⟩
          · exact ⟨1, one_mem_pairings _, by
              rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
              have c5 := w1le6 x5 l5 (by linarith only [b4, o4])
              linarith only [q0, q1, q2, q3, q4, c5]⟩
        · exact ⟨1, one_mem_pairings _, by
            rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
            have c4 := w1le6 x4 l4 (by linarith only [b3, o3])
            have c5 := w1le6 x5 l5 (by linarith only [b3, o3, o4])
            linarith only [q0, q1, q2, q3, c4, c5]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le6 x4 l4 (by linarith only [b2, o2, o3])
          have c5 := w1le6 x5 l5 (by linarith only [b2, o2, o3, o4])
          linarith only [q0, q1, q2, c3, c4, c5]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le6 x4 l4 (by linarith only [b1, o1, o2, o3])
        have c5 := w1le6 x5 l5 (by linarith only [b1, o1, o2, o3, o4])
        linarith only [q0, q1, c2, c3, c4, c5]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
      have c1 := w1le6 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le6 x2 l2 (by linarith only [b0, o0, o1])
      have c3 := w1le6 x3 l3 (by linarith only [b0, o0, o1, o2])
      have c4 := w1le6 x4 l4 (by linarith only [b0, o0, o1, o2, o3])
      have c5 := w1le6 x5 l5 (by linarith only [b0, o0, o1, o2, o3, o4])
      linarith only [q0, c1, c2, c3, c4, c5]⟩
theorem reduce (S : List ℝ) (hsort : S.Pairwise (fun a b => b ≤ a))
    (hr : ∀ x ∈ S, 1 / 7 < x ∧ x ≤ 1 / 2) (hs : S.sum ≤ 1) :
    ∃ σ ∈ pairings S.length, w12 S σ ≤ 71 / 60 := by
  match S, hsort, hr, hs with
  | [], _, _, _ => exact ⟨1, one_mem_pairings _, by rw [w12_one, sum_w1]; norm_num⟩
  | [x0], hsort, hr, hs =>
    obtain ⟨l0, u0⟩ := hr x0 (by simp)
    simp only [List.sum_cons, List.sum_nil] at hs
    exact core1 x0 l0 u0  (by linarith)
  | [x0, x1], hsort, hr, hs =>
    obtain ⟨l0, u0⟩ := hr x0 (by simp)
    obtain ⟨l1, u1⟩ := hr x1 (by simp)
    have o0 : x1 ≤ x0 := List.rel_of_pairwise_cons hsort (by simp)
    simp only [List.sum_cons, List.sum_nil] at hs
    exact core2 x0 x1 l0 l1 u0 o0 (by linarith)
  | [x0, x1, x2], hsort, hr, hs =>
    obtain ⟨l0, u0⟩ := hr x0 (by simp)
    obtain ⟨l1, u1⟩ := hr x1 (by simp)
    obtain ⟨l2, u2⟩ := hr x2 (by simp)
    have o0 : x1 ≤ x0 := List.rel_of_pairwise_cons hsort (by simp)
    have o1 : x2 ≤ x1 := List.rel_of_pairwise_cons (hsort).of_cons (by simp)
    simp only [List.sum_cons, List.sum_nil] at hs
    exact core3 x0 x1 x2 l0 l1 l2 u0 o0 o1 (by linarith)
  | [x0, x1, x2, x3], hsort, hr, hs =>
    obtain ⟨l0, u0⟩ := hr x0 (by simp)
    obtain ⟨l1, u1⟩ := hr x1 (by simp)
    obtain ⟨l2, u2⟩ := hr x2 (by simp)
    obtain ⟨l3, u3⟩ := hr x3 (by simp)
    have o0 : x1 ≤ x0 := List.rel_of_pairwise_cons hsort (by simp)
    have o1 : x2 ≤ x1 := List.rel_of_pairwise_cons (hsort).of_cons (by simp)
    have o2 : x3 ≤ x2 := List.rel_of_pairwise_cons ((hsort).of_cons).of_cons (by simp)
    simp only [List.sum_cons, List.sum_nil] at hs
    exact core4 x0 x1 x2 x3 l0 l1 l2 l3 u0 o0 o1 o2 (by linarith)
  | [x0, x1, x2, x3, x4], hsort, hr, hs =>
    obtain ⟨l0, u0⟩ := hr x0 (by simp)
    obtain ⟨l1, u1⟩ := hr x1 (by simp)
    obtain ⟨l2, u2⟩ := hr x2 (by simp)
    obtain ⟨l3, u3⟩ := hr x3 (by simp)
    obtain ⟨l4, u4⟩ := hr x4 (by simp)
    have o0 : x1 ≤ x0 := List.rel_of_pairwise_cons hsort (by simp)
    have o1 : x2 ≤ x1 := List.rel_of_pairwise_cons (hsort).of_cons (by simp)
    have o2 : x3 ≤ x2 := List.rel_of_pairwise_cons ((hsort).of_cons).of_cons (by simp)
    have o3 : x4 ≤ x3 := List.rel_of_pairwise_cons (((hsort).of_cons).of_cons).of_cons (by simp)
    simp only [List.sum_cons, List.sum_nil] at hs
    exact core5 x0 x1 x2 x3 x4 l0 l1 l2 l3 l4 u0 o0 o1 o2 o3 (by linarith)
  | [x0, x1, x2, x3, x4, x5], hsort, hr, hs =>
    obtain ⟨l0, u0⟩ := hr x0 (by simp)
    obtain ⟨l1, u1⟩ := hr x1 (by simp)
    obtain ⟨l2, u2⟩ := hr x2 (by simp)
    obtain ⟨l3, u3⟩ := hr x3 (by simp)
    obtain ⟨l4, u4⟩ := hr x4 (by simp)
    obtain ⟨l5, u5⟩ := hr x5 (by simp)
    have o0 : x1 ≤ x0 := List.rel_of_pairwise_cons hsort (by simp)
    have o1 : x2 ≤ x1 := List.rel_of_pairwise_cons (hsort).of_cons (by simp)
    have o2 : x3 ≤ x2 := List.rel_of_pairwise_cons ((hsort).of_cons).of_cons (by simp)
    have o3 : x4 ≤ x3 := List.rel_of_pairwise_cons (((hsort).of_cons).of_cons).of_cons (by simp)
    have o4 : x5 ≤ x4 := List.rel_of_pairwise_cons ((((hsort).of_cons).of_cons).of_cons).of_cons (by simp)
    simp only [List.sum_cons, List.sum_nil] at hs
    exact core6 x0 x1 x2 x3 x4 x5 l0 l1 l2 l3 l4 l5 u0 o0 o1 o2 o3 o4 (by linarith)
  | x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: rest, _, hr, hs =>
    exfalso
    obtain ⟨l0, -⟩ := hr x0 (by simp)
    obtain ⟨l1, -⟩ := hr x1 (by simp)
    obtain ⟨l2, -⟩ := hr x2 (by simp)
    obtain ⟨l3, -⟩ := hr x3 (by simp)
    obtain ⟨l4, -⟩ := hr x4 (by simp)
    obtain ⟨l5, -⟩ := hr x5 (by simp)
    obtain ⟨l6, -⟩ := hr x6 (by simp)
    have hrest : 0 ≤ rest.sum := List.sum_nonneg (fun x hx => le_of_lt (lt_trans (by norm_num) (hr x (by simp [hx])).1))
    simp only [List.sum_cons] at hs
    linarith

end P6c9b

open BinPacking.SmallItems in
theorem sol_6c9b70f9 (X : List ℝ) (hX : ∀ x ∈ X, 1 / 7 < x ∧ x ≤ 1 / 2)
    (hsum : X.sum ≤ 1) :
    W X ≤ 71 / 60 := by
  have hp : (sortDesc X).Perm X := List.mergeSort_perm _ _
  have hsorted : (sortDesc X).Pairwise (fun a b => b ≤ a) := by
    have h := List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; linarith)
      (fun a b => by simpa using le_total b a) X
    simpa [sortDesc] using h
  obtain ⟨σ, hσ, hw⟩ := P6c9b.reduce (sortDesc X) hsorted (fun x hx => hX x (hp.subset hx))
    (by rw [hp.sum_eq]; exact hsum)
  exact le_trans (Finset.inf'_le _ hσ) hw


namespace WLE_4c187921
open BinPacking.SmallItems

/-- `w₁₂` for a value function on `Fin n`. -/
noncomputable def wf (n : ℕ) (h : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => σ i = i), w1 (h i)) +
    ∑ i ∈ Finset.univ.filter (fun i => i < σ i), w2 (h i) (h (σ i))

lemma inv_of_sq {n : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : σ * σ = 1) (i : Fin n) : σ (σ i) = i := by
  have := congrArg (fun τ : Equiv.Perm (Fin n) => τ i) hσ
  simpa [Equiv.Perm.mul_apply] using this

lemma exists_w12_eq_wf (n : ℕ) (h : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (hσ : σ * σ = 1)
    (S : List ℝ) (hS : S = List.ofFn h) :
    ∃ σ' ∈ pairings S.length, w12 S σ' = wf n h σ := by
  subst hS
  let e : Fin (List.ofFn h).length ≃ Fin n := finCongr List.length_ofFn
  refine ⟨e.trans (σ.trans e.symm), ?_, ?_⟩
  · simp only [pairings, Finset.mem_filter, Finset.mem_univ, true_and]
    ext x
    simp [e, Equiv.Perm.mul_apply, inv_of_sq σ hσ]
  · unfold w12 wf
    congr 1
    · apply Finset.sum_equiv e
      · intro x; simp [e, Fin.ext_iff]
      · intro x _; simp [e]; rfl
    · apply Finset.sum_equiv e
      · intro x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Iff.rfl
      · intro x _; simp [e]; rfl

lemma W_le_wf (Z : List ℝ) (n : ℕ) (h : Fin n → ℝ) (hZ : sortDesc Z = List.ofFn h)
    (σ : Equiv.Perm (Fin n)) (hσ : σ * σ = 1) : W Z ≤ wf n h σ := by
  obtain ⟨σ', hσ', heq⟩ := exists_w12_eq_wf n h σ hσ (sortDesc Z) hZ
  unfold W
  rw [← heq]
  exact Finset.inf'_le _ hσ'

lemma sortDesc_pairwise (X : List ℝ) : (sortDesc X).Pairwise (fun a b => b ≤ a) := by
  have h := List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; linarith)
    (fun a b => by simpa using le_total b a) X
  simpa [sortDesc] using h

lemma sortDesc_eq_of (Z Y : List ℝ) (hp : Z.Perm Y) (hY : Y.Pairwise (fun a b => b ≤ a)) :
    sortDesc Z = Y := by
  have hp' : (sortDesc Z).Perm Y := (List.mergeSort_perm _ _).trans hp
  exact hp'.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h2 h1) (sortDesc_pairwise Z) hY

lemma W_perm (X Y : List ℝ) (h : X.Perm Y) : W X = W Y := by
  have : sortDesc X = sortDesc Y :=
    sortDesc_eq_of X (sortDesc Y) (h.trans (List.mergeSort_perm _ _).symm) (sortDesc_pairwise Y)
  have key : ∀ S T : List ℝ, S = T →
      (pairings S.length).inf' ⟨1, by simp [pairings]⟩ (w12 S) =
        (pairings T.length).inf' ⟨1, by simp [pairings]⟩ (w12 T) := by
    rintro S T rfl; rfl
  exact key _ _ this

lemma sort_key {n : ℕ} (g : Fin n → ℝ) (j k : Fin n) :
    (Tuple.sort (fun i => -g i)).symm j < (Tuple.sort (fun i => -g i)).symm k ↔
      g k < g j ∨ (g j = g k ∧ j < k) := by
  obtain ⟨hmono, htie⟩ := (Tuple.eq_sort_iff (f := fun i => -g i)
    (σ := Tuple.sort (fun i => -g i))).mp rfl
  have fwd : ∀ a b : Fin n, a < b →
      g (Tuple.sort (fun i => -g i) b) < g (Tuple.sort (fun i => -g i) a) ∨
      (g (Tuple.sort (fun i => -g i) a) = g (Tuple.sort (fun i => -g i) b) ∧
        Tuple.sort (fun i => -g i) a < Tuple.sort (fun i => -g i) b) := by
    intro a b hab
    have h1 : -g (Tuple.sort (fun i => -g i) a) ≤ -g (Tuple.sort (fun i => -g i) b) := hmono hab.le
    rcases lt_or_eq_of_le h1 with h2 | h2
    · left; linarith
    · right; exact ⟨by linarith, htie a b hab h2⟩
  constructor
  · intro hlt
    have := fwd _ _ hlt
    simpa using this
  · intro hor
    rcases lt_trichotomy ((Tuple.sort (fun i => -g i)).symm j)
      ((Tuple.sort (fun i => -g i)).symm k) with h | h | h
    · exact h
    · exfalso
      have hjk : j = k := by simpa using congrArg (Tuple.sort (fun i => -g i)) h
      subst hjk
      rcases hor with h' | h'
      · exact lt_irrefl _ h'
      · exact lt_irrefl _ h'.2
    · exfalso
      have := fwd _ _ h
      simp only [Equiv.apply_symm_apply] at this
      rcases hor with h' | h' <;> rcases this with h'' | h''
      · linarith
      · linarith [h''.1]
      · linarith [h'.1]
      · exact lt_asymm h'.2 h''.2

lemma orient_iff {n : ℕ} (g : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (hinv : ∀ i, σ (σ i) = i)
    (hor : ∀ j, j < σ j → g (σ j) ≤ g j) (j : Fin n) :
    (g (σ j) < g j ∨ (g j = g (σ j) ∧ j < σ j)) ↔ j < σ j := by
  constructor
  · rintro (h | h)
    · rcases lt_trichotomy j (σ j) with h1 | h1 | h1
      · exact h1
      · exfalso; rw [← h1] at h; exact lt_irrefl _ h
      · exfalso
        have := hor (σ j) (by rw [hinv]; exact h1)
        rw [hinv] at this
        linarith
    · exact h.2
  · intro h
    rcases lt_or_eq_of_le (hor j h) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨h1.symm, h⟩

lemma wf_reindex {n : ℕ} (g : Fin n → ℝ) (σT : Equiv.Perm (Fin n)) (hinv : ∀ i, σT (σT i) = i)
    (hor : ∀ j, j < σT j → g (σT j) ≤ g j) :
    wf n (g ∘ Tuple.sort (fun i => -g i))
      ((Tuple.sort (fun i => -g i)).trans (σT.trans (Tuple.sort (fun i => -g i)).symm)) =
      wf n g σT := by
  unfold wf
  congr 1
  · apply Finset.sum_equiv (Tuple.sort (fun i => -g i))
    · intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.trans_apply,
        Equiv.symm_apply_eq]
    · intro i _; rfl
  · apply Finset.sum_equiv (Tuple.sort (fun i => -g i))
    · intro i
      rw [Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, Equiv.trans_apply]
      rw [← orient_iff g σT hinv hor (Tuple.sort (fun i => -g i) i), ← sort_key g,
        Equiv.symm_apply_apply]
    · intro i _
      simp

lemma wf_split (SX SY : List ℝ) (σX : Equiv.Perm (Fin SX.length)) (σY : Equiv.Perm (Fin SY.length))
    (hX : SX.Pairwise (fun a b => b ≤ a)) (hY : SY.Pairwise (fun a b => b ≤ a))
    (hσX : σX * σX = 1) (hσY : σY * σY = 1) :
    ∃ (n : ℕ) (h : Fin n → ℝ) (σ : Equiv.Perm (Fin n)), σ * σ = 1 ∧
      (List.ofFn h).Perm (SX ++ SY) ∧ (List.ofFn h).Pairwise (fun a b => b ≤ a) ∧
      wf n h σ = w12 SX σX + w12 SY σY := by
  have iX := inv_of_sq σX hσX
  have iY := inv_of_sq σY hσY
  let g : Fin (SX.length + SY.length) → ℝ := Fin.append SX.get SY.get
  let σT : Equiv.Perm (Fin (SX.length + SY.length)) :=
    finSumFinEquiv.symm.trans ((σX.sumCongr σY).trans finSumFinEquiv)
  have hTl : ∀ i, σT (Fin.castAdd SY.length i) = Fin.castAdd SY.length (σX i) := by
    intro i; simp [σT]
  have hTr : ∀ i, σT (Fin.natAdd SX.length i) = Fin.natAdd SX.length (σY i) := by
    intro i; simp [σT]
  have hgl : ∀ i, g (Fin.castAdd SY.length i) = SX.get i := by intro i; simp [g]
  have hgr : ∀ i, g (Fin.natAdd SX.length i) = SY.get i := by intro i; simp [g]
  have hTinv : ∀ i, σT (σT i) = i := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [hTl, hTl, iX]
    · rw [hTr, hTr, iY]
  have hor : ∀ j, j < σT j → g (σT j) ≤ g j := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [hTl, hgl, hgl]
      intro hlt
      have hlt' : i < σX i := by
        rw [Fin.lt_def] at hlt ⊢; simpa using hlt
      exact List.pairwise_iff_get.mp hX i (σX i) hlt'
    · rw [hTr, hgr, hgr]
      intro hlt
      have hlt' : i < σY i := by
        rw [Fin.lt_def] at hlt ⊢; simpa using hlt
      exact List.pairwise_iff_get.mp hY i (σY i) hlt'
  refine ⟨SX.length + SY.length, g ∘ Tuple.sort (fun i => -g i),
    (Tuple.sort (fun i => -g i)).trans (σT.trans (Tuple.sort (fun i => -g i)).symm), ?_, ?_, ?_, ?_⟩
  · ext i
    simp [Equiv.Perm.mul_apply, hTinv]
  · have h1 := Equiv.Perm.ofFn_comp_perm (Tuple.sort (fun i => -g i)) g
    have h2 : List.ofFn g = SX ++ SY := by
      simp only [g, List.ofFn_fin_append, List.ofFn_get]
    rw [← h2]; exact h1
  · rw [List.pairwise_ofFn]
    intro i j hij
    have := Tuple.monotone_sort (fun i => -g i) hij.le
    simp only [Function.comp_apply] at this ⊢
    linarith
  · rw [wf_reindex g σT hTinv hor]
    unfold wf w12
    simp only [Finset.sum_filter]
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [hTl, hTr, hgl, hgr]
    have e1 : ∀ i : Fin SX.length,
        (Fin.castAdd SY.length (σX i) = Fin.castAdd SY.length i ↔ σX i = i) := by
      intro i; simp [Fin.ext_iff]
    have e2 : ∀ i : Fin SY.length,
        (Fin.natAdd SX.length (σY i) = Fin.natAdd SX.length i ↔ σY i = i) := by
      intro i; simp [Fin.ext_iff]
    have e3 : ∀ i : Fin SX.length,
        (Fin.castAdd SY.length i < Fin.castAdd SY.length (σX i) ↔ i < σX i) := by
      intro i; simp only [Fin.lt_def, Fin.val_castAdd]
    have e4 : ∀ i : Fin SY.length,
        (Fin.natAdd SX.length i < Fin.natAdd SX.length (σY i) ↔ i < σY i) := by
      intro i; simp only [Fin.lt_def, Fin.val_natAdd]; constructor <;> intro h <;> omega
    simp only [e1, e2, e3, e4]
    ring

lemma W_append_le (X Y : List ℝ) : W (X ++ Y) ≤ W X + W Y := by
  obtain ⟨σX, hσXm, hX⟩ := Finset.exists_mem_eq_inf' (s := pairings (sortDesc X).length)
    ⟨1, by simp [pairings]⟩ (w12 (sortDesc X))
  obtain ⟨σY, hσYm, hY⟩ := Finset.exists_mem_eq_inf' (s := pairings (sortDesc Y).length)
    ⟨1, by simp [pairings]⟩ (w12 (sortDesc Y))
  have hWX : W X = w12 (sortDesc X) σX := hX
  have hWY : W Y = w12 (sortDesc Y) σY := hY
  simp only [pairings, Finset.mem_filter, Finset.mem_univ, true_and] at hσXm hσYm
  obtain ⟨n, h, σ, hσ, hp, hs, heq⟩ := wf_split (sortDesc X) (sortDesc Y) σX σY
    (sortDesc_pairwise X) (sortDesc_pairwise Y) hσXm hσYm
  have hZ : sortDesc (X ++ Y) = List.ofFn h := by
    apply sortDesc_eq_of _ _ _ hs
    refine List.Perm.trans ?_ hp.symm
    exact ((List.mergeSort_perm _ _).append (List.mergeSort_perm _ _)).symm
  rw [hWX, hWY, ← heq]
  exact W_le_wf (X ++ Y) n h hZ σ hσ

lemma w12_nil (S : List ℝ) (hS : S = []) (σ : Equiv.Perm (Fin S.length)) : w12 S σ = 0 := by
  subst hS
  simp [w12]

lemma W_nil_le : W [] ≤ 0 := by
  unfold W
  have hm : (1 : Equiv.Perm (Fin (sortDesc ([] : List ℝ)).length)) ∈
      pairings (sortDesc ([] : List ℝ)).length := by simp [pairings]
  refine (Finset.inf'_le _ hm).trans (le_of_eq ?_)
  exact w12_nil _ (by simp [sortDesc]) _

lemma W_le_bins {ι : Type}
    (hbin : ∀ Y : List ℝ, (∀ y ∈ Y, 1 / 7 < y ∧ y ≤ 1 / 2) → Y.sum ≤ 1 → W Y ≤ 71 / 60)
    (v : ι → ℝ) (f : ι → ℕ) : ∀ (b : ℕ) (Q : List ι), (∀ i ∈ Q, f i < b) →
    (∀ i ∈ Q, 1 / 7 < v i ∧ v i ≤ 1 / 2) →
    (∀ j : ℕ, ((Q.filter (fun i => decide (f i = j))).map v).sum ≤ 1) →
    W (Q.map v) ≤ 71 / 60 * (b : ℝ) := by
  intro b
  induction b with
  | zero =>
    intro Q hf _ _
    have hQ : Q = [] := List.eq_nil_iff_forall_not_mem.mpr
      (fun i hi => by have := hf i hi; omega)
    subst hQ
    simpa using W_nil_le
  | succ b ih =>
    intro Q hf hv hs
    have hp : (Q.map v).Perm ((Q.filter (fun i => decide (f i = b))).map v ++
        (Q.filter (fun i => !decide (f i = b))).map v) := by
      rw [← List.map_append]
      exact ((List.filter_append_perm _ Q).symm).map v
    rw [W_perm _ _ hp]
    have h1 : W ((Q.filter (fun i => decide (f i = b))).map v) ≤ 71 / 60 := by
      apply hbin
      · intro y hy
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
        exact hv i (List.mem_of_mem_filter hi)
      · exact hs b
    have h2 : W ((Q.filter (fun i => !decide (f i = b))).map v) ≤ 71 / 60 * (b : ℝ) := by
      apply ih
      · intro i hi
        have hm := List.mem_filter.mp hi
        have h3 := hf i hm.1
        have h4 : f i ≠ b := by simpa using hm.2
        omega
      · intro i hi
        exact hv i (List.mem_of_mem_filter hi)
      · intro j
        refine le_trans ?_ (hs j)
        apply List.Sublist.sum_le_sum
        · exact (List.Sublist.filter _ List.filter_sublist).map v
        · intro y hy
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
          linarith [hv i (List.mem_of_mem_filter hi)]
    calc W ((Q.filter (fun i => decide (f i = b))).map v ++
          (Q.filter (fun i => !decide (f i = b))).map v)
        ≤ W ((Q.filter (fun i => decide (f i = b))).map v) +
          W ((Q.filter (fun i => !decide (f i = b))).map v) := W_append_le _ _
      _ ≤ 71 / 60 + 71 / 60 * (b : ℝ) := add_le_add h1 h2
      _ = 71 / 60 * ((b + 1 : ℕ) : ℝ) := by push_cast; ring

lemma W_le_of_assign
    (hbin : ∀ Y : List ℝ, (∀ y ∈ Y, 1 / 7 < y ∧ y ≤ 1 / 2) → Y.sum ≤ 1 → W Y ≤ 71 / 60)
    (X : List ℝ) (hX : ∀ x ∈ X, 1 / 7 < x ∧ x ≤ 1 / 2) (b : ℕ) (f : Fin X.length → Fin b)
    (hf : ∀ j : Fin b, ∑ i ∈ Finset.univ.filter (fun i => f i = j), X.get i ≤ 1) :
    W X ≤ 71 / 60 * (b : ℝ) := by
  have hmap : (List.finRange X.length).map X.get = X := List.map_get_finRange X
  have key := W_le_bins hbin X.get (fun i => ((f i : Fin b) : ℕ)) b (List.finRange X.length)
    (fun i _ => (f i).isLt) (fun i _ => hX _ (List.get_mem X i)) ?_
  · rwa [hmap] at key
  · intro j
    by_cases hj : j < b
    · have hfs := hf ⟨j, hj⟩
      have hnd : ((List.finRange X.length).filter
          (fun i => decide (((f i : Fin b) : ℕ) = j))).Nodup :=
        (List.nodup_finRange _).filter _
      rw [← List.sum_toFinset _ hnd]
      have hset : ((List.finRange X.length).filter
          (fun i => decide (((f i : Fin b) : ℕ) = j))).toFinset =
          Finset.univ.filter (fun i => f i = ⟨j, hj⟩) := by
        ext i; simp [Fin.ext_iff]
      rw [hset]; exact hfs
    · have : (List.finRange X.length).filter (fun i => decide (((f i : Fin b) : ℕ) = j)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro i _
        have := (f i).isLt
        simp only [decide_eq_true_eq]
        omega
      rw [this]; simp

lemma W_le_opt
    (hbin : ∀ Y : List ℝ, (∀ y ∈ Y, 1 / 7 < y ∧ y ≤ 1 / 2) → Y.sum ≤ 1 → W Y ≤ 71 / 60)
    (X : List ℝ) (hX : ∀ x ∈ X, 1 / 7 < x ∧ x ≤ 1 / 2) :
    W X ≤ 71 / 60 * (optBins X : ℝ) := by
  have hne : {b : ℕ | ∃ f : Fin X.length → Fin b, ∀ j : Fin b,
      ∑ i ∈ Finset.univ.filter (fun i => f i = j), X.get i ≤ 1}.Nonempty := by
    refine ⟨X.length, id, fun j => ?_⟩
    have : Finset.univ.filter (fun i : Fin X.length => id i = j) = {j} := by ext i; simp
    rw [this, Finset.sum_singleton]
    linarith [hX _ (List.get_mem X j)]
  obtain ⟨f, hf⟩ := Nat.sInf_mem hne
  exact W_le_of_assign hbin X hX _ f hf

end WLE_4c187921


open BinPacking.SmallItems in
theorem solution (L : List ℝ) (hL : IsList L) (hhalf : ∀ a ∈ L, a ≤ 1 / 2) :
    (FFD L : ℝ) ≤ 71 / 60 * (optBins L : ℝ) + 5 := by
  by_contra hcon
  push_neg at hcon
  have h1 := sol_e3877310 (71 / 60) 5 (by norm_num) (by norm_num) L hL hcon
  have hmem : ∀ a ∈ L.filter (fun a => decide ((71 / 60 - 1) / (71 / 60) < a)),
      (71 / 60 - 1) / (71 / 60) < a ∧ a ∈ L := by
    intro a ha
    have := List.mem_filter.mp ha
    exact ⟨by simpa using this.2, this.1⟩
  have hr : ∀ a ∈ L.filter (fun a => decide ((71 / 60 - 1) / (71 / 60) < a)),
      1 / 7 < a ∧ a ≤ 1 / 2 := by
    intro a ha
    have h0 := (hmem a ha).1
    refine ⟨?_, hhalf a (hmem a ha).2⟩
    norm_num at h0 ⊢
    linarith
  have hLl : IsList (L.filter (fun a => decide ((71 / 60 - 1) / (71 / 60) < a))) :=
    fun a ha => hL a (hmem a ha).2
  have h2 := WFFD_9ce81529.W_ge 7 (by norm_num) _ hLl (by
    intro a ha
    have := hr a ha
    exact ⟨by norm_num; linarith [this.1], this.2⟩)
  have h3 := WLE_4c187921.W_le_opt (fun Y hY hs => sol_6c9b70f9 Y hY hs) _ hr
  push_cast at h2
  linarith
