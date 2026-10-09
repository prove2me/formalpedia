-- Prove2me | solution 1 for BinPacking.SmallItems.w12_ge_basic_weight
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T11:44:27.979451+00:00
-- url     : https://prove2.me/submissions/adf9c5ed-3721-4f4c-92f1-4d8c12de1cdf

import Mathlib
import Definitions.Def_BinPacking_SmallItems_Model
import Definitions.Def_BinPacking_SmallItems_Weight

set_option autoImplicit false

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

open BinPacking.SmallItems in
theorem solution (N : ℕ) (hN : 4 ≤ N) (L : List ℝ) (hL : IsList L)
    (hrange : ∀ a ∈ L, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2)
    (σ : Equiv.Perm (Fin (sortDesc L).length)) (hσ : σ ∈ pairings (sortDesc L).length) :
    w12 (sortDesc L) σ ≥
      ∑ i ∈ basic L, w1 ((sortDesc L).get i) - ∑ j ∈ Finset.Icc 3 (N - 1), 1 / (j : ℝ) := by
  exact C4Aux_998ce8a1.main N hN L hrange σ hσ
