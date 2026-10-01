-- Prove2me | solution 1 for BinPacking.SmallItems.basic_weight_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T09:16:21.173471+00:00
-- url     : https://prove2.me/submissions/eec5bef1-9f19-4175-a32d-f939ec4090c6

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
theorem solution (N : ℕ) (hN : 4 ≤ N) (L : List ℝ) (hL : IsList L)
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
