-- Prove2me | solution 1 for BinPacking.Decreasing.bfd_le_ffd
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T02:45:54.156264+00:00
-- url     : https://prove2.me/submissions/8bbdca3d-17df-402b-8d57-976a01c2df7e

import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model

set_option autoImplicit false

namespace BinPacking.Decreasing.CapModel

open BinPacking.Decreasing

/-- Free-capacity form of first fit: `caps` lists `1 - level` of every bin in index order. -/
noncomputable def capFF (caps : List ℝ) (a : ℝ) : List ℝ :=
  let j := caps.findIdx (fun c => decide (a ≤ c))
  if j < caps.length then caps.modify j (fun c => c - a) else caps ++ [1 - a]

/-- Free-capacity form of best fit: the least index among the tightest bins that still fit. -/
noncomputable def capBF (caps : List ℝ) (a : ℝ) : List ℝ :=
  let j := caps.findIdx (fun c => decide (a ≤ c ∧ ∀ c' ∈ caps, a ≤ c' → c ≤ c'))
  if j < caps.length then caps.modify j (fun c => c - a) else caps ++ [1 - a]

/-- The capacity map of a bin list. -/
noncomputable def capsOf (bins : List (List ℝ)) : List ℝ := bins.map (fun B => 1 - B.sum)

theorem placeAt_caps (bins : List (List ℝ)) (j : ℕ) (a : ℝ) :
    capsOf (placeAt bins j a) =
      if j < bins.length then (capsOf bins).modify j (fun c => c - a)
      else capsOf bins ++ [1 - a] := by
  unfold placeAt capsOf
  split_ifs with hj
  · apply List.ext_getElem
    · simp
    · intro n h1 h2
      simp only [List.getElem_map, List.getElem_mapIdx, List.getElem_modify]
      by_cases e : n = j
      · subst e; simp [List.sum_append]; ring
      · rw [if_neg e, if_neg (fun h => e h.symm)]
  · simp

theorem ffChoice_caps (bins : List (List ℝ)) (a : ℝ) :
    ffChoice bins a = (capsOf bins).findIdx (fun c => decide (a ≤ c)) := by
  unfold ffChoice capsOf
  rw [List.findIdx_map]
  congr 1
  funext B
  simp only [Function.comp, decide_eq_decide]
  constructor <;> intro h <;> linarith

theorem bfChoice_caps (bins : List (List ℝ)) (a : ℝ) :
    bfChoice bins a = (capsOf bins).findIdx
      (fun c => decide (a ≤ c ∧ ∀ c' ∈ capsOf bins, a ≤ c' → c ≤ c')) := by
  unfold bfChoice
  conv_rhs => unfold capsOf
  rw [List.findIdx_map]
  congr 1
  funext B
  simp only [Function.comp, decide_eq_decide, capsOf, List.forall_mem_map]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, fun B' hB' h3 => ?_⟩
    have := h2 B' hB' (by linarith)
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, fun B' hB' h3 => ?_⟩
    have := h2 B' hB' (by linarith)
    linarith

theorem capsOf_length (bins : List (List ℝ)) : (capsOf bins).length = bins.length := by
  simp [capsOf]

theorem step_ff (bins : List (List ℝ)) (a : ℝ) :
    capsOf (placeAt bins (ffChoice bins a) a) = capFF (capsOf bins) a := by
  rw [placeAt_caps, ffChoice_caps, capFF, capsOf_length]

theorem step_bf (bins : List (List ℝ)) (a : ℝ) :
    capsOf (placeAt bins (bfChoice bins a) a) = capBF (capsOf bins) a := by
  rw [placeAt_caps, bfChoice_caps, capBF, capsOf_length]

theorem foldl_ff (S : List ℝ) : ∀ bins : List (List ℝ),
    capsOf (S.foldl (fun bins a => placeAt bins (ffChoice bins a) a) bins) =
      S.foldl capFF (capsOf bins) := by
  induction S with
  | nil => intro bins; rfl
  | cons a t ih => intro bins; simp only [List.foldl_cons]; rw [ih, step_ff]

theorem foldl_bf (S : List ℝ) : ∀ bins : List (List ℝ),
    capsOf (S.foldl (fun bins a => placeAt bins (bfChoice bins a) a) bins) =
      S.foldl capBF (capsOf bins) := by
  induction S with
  | nil => intro bins; rfl
  | cons a t ih => intro bins; simp only [List.foldl_cons]; rw [ih, step_bf]

/-- BRIDGE: the bin levels of the first-fit run are the capacity-form run. -/
theorem run_ff_caps (S : List ℝ) :
    (run ffChoice S).map (fun B => 1 - B.sum) = S.foldl capFF [] :=
  foldl_ff S []

/-- BRIDGE: the bin levels of the best-fit run are the capacity-form run. -/
theorem run_bf_caps (S : List ℝ) :
    (run bfChoice S).map (fun B => 1 - B.sum) = S.foldl capBF [] :=
  foldl_bf S []

theorem FF_eq_caps (S : List ℝ) : FF S = (S.foldl capFF []).length := by
  rw [← run_ff_caps, List.length_map]; rfl

theorem BF_eq_caps (S : List ℝ) : BF S = (S.foldl capBF []).length := by
  rw [← run_bf_caps, List.length_map]; rfl

end BinPacking.Decreasing.CapModel


namespace BinPacking.Decreasing.FFBigs

open BinPacking.Decreasing

/-- Invariant of a first-fit run on a nonincreasing list: bins are nonempty with all items at
least `a` (the next item), and every bin with level `≤ 2/3` has level at most that of every
earlier bin. -/
def Inv2 (bins : List (List ℝ)) (a : ℝ) : Prop :=
  (∀ B ∈ bins, B ≠ [] ∧ ∀ x ∈ B, a ≤ x) ∧
  (∀ (j j' : ℕ) (hj : j < j') (hj' : j' < bins.length),
    (bins[j']'hj').sum ≤ 2 / 3 → (bins[j']'hj').sum ≤ (bins[j]'(by omega)).sum)

theorem sum_ge_of (B : List ℝ) (a : ℝ) (ha : 0 < a) (hne : B ≠ []) (hB : ∀ x ∈ B, a ≤ x) :
    a ≤ B.sum := by
  match B, hne, hB with
  | x :: t, _, hB =>
    have h0 : 0 ≤ t.sum := List.sum_nonneg (fun z hz => by
      have := hB z (by simp [hz]); linarith)
    have := hB x (by simp)
    simp only [List.sum_cons]; linarith

theorem inv2_step (bins : List (List ℝ)) (y a : ℝ) (hI : Inv2 bins y) (hay : a ≤ y)
    (hy0 : 0 < y) : Inv2 (placeAt bins (ffChoice bins y) y) a := by
  obtain ⟨h1, h2⟩ := hI
  have hsum : ∀ (k : ℕ) (hk : k < bins.length), y ≤ (bins[k]'hk).sum := fun k hk => by
    obtain ⟨hne, hel⟩ := h1 _ (List.getElem_mem hk)
    exact sum_ge_of _ y hy0 hne hel
  unfold placeAt
  split_ifs with hc
  · -- joins an existing bin c
    set c := ffChoice bins y with hcdef
    have hnot : ∀ (j : ℕ) (hj : j < c), ¬ ((bins[j]'(by omega)).sum + y ≤ 1) := by
      intro j hj
      have := List.not_of_lt_findIdx (p := fun B : List ℝ => decide (B.sum + y ≤ 1))
        (xs := bins) (i := j) (show j < List.findIdx (fun B : List ℝ => decide (B.sum + y ≤ 1)) bins from hj)
      simpa using this
    refine ⟨?_, ?_⟩
    · intro B hB
      obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hB
      simp only [List.getElem_mapIdx]
      have hm' : m < bins.length := by simpa using hm
      obtain ⟨hne, hel⟩ := h1 _ (List.getElem_mem hm')
      split_ifs
      · refine ⟨by simp, ?_⟩
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact le_trans hay (hel x hx)
        · simp at hx; subst hx; exact hay
      · exact ⟨hne, fun x hx => le_trans hay (hel x hx)⟩
    · intro j j' hj hj' hle
      have hj'b : j' < bins.length := by simpa using hj'
      have hjb : j < bins.length := by omega
      simp only [List.getElem_mapIdx] at hle ⊢
      by_cases e1 : j' = c
      · have e2 : j ≠ c := by omega
        rw [if_pos e1] at hle ⊢
        rw [if_neg e2]
        simp only [List.sum_append, List.sum_singleton] at hle ⊢
        have hs := hsum j' hj'b
        have hn := hnot j (by omega)
        have hy3 : y ≤ 1 / 3 := by linarith
        linarith
      · rw [if_neg e1] at hle ⊢
        by_cases e2 : j = c
        · rw [if_pos e2]
          simp only [List.sum_append, List.sum_singleton]
          have := h2 j j' hj hj'b hle
          linarith
        · rw [if_neg e2]
          exact h2 j j' hj hj'b hle
  · -- opens a new bin
    refine ⟨?_, ?_⟩
    · intro B hB
      rcases List.mem_append.mp hB with hB | hB
      · obtain ⟨hne, hel⟩ := h1 B hB
        exact ⟨hne, fun x hx => le_trans hay (hel x hx)⟩
      · simp at hB; subst hB
        refine ⟨by simp, ?_⟩
        intro x hx; simp at hx; subst hx; exact hay
    · intro j j' hj hj' hle
      simp only [List.length_append, List.length_singleton] at hj'
      by_cases hj'' : j' < bins.length
      · simp only [List.getElem_append_left hj'', List.getElem_append_left (show j < bins.length by omega)] at hle ⊢
        exact h2 j j' hj hj'' hle
      · have e : j' = bins.length := by omega
        subst e
        simp only [List.getElem_append_left (show j < bins.length by omega),
          List.getElem_append_right (le_refl _)] at hle ⊢
        simp only [Nat.sub_self, List.getElem_cons_zero, List.sum_singleton] at hle ⊢
        exact hsum j (by omega)

theorem run_append (c : List (List ℝ) → ℝ → ℕ) (l : List ℝ) (y : ℝ) :
    run c (l ++ [y]) = placeAt (run c l) (c (run c l) y) y := by
  simp [run, List.foldl_append]

theorem inv2_run (l : List ℝ) : ∀ (a : ℝ), 0 < a → (∀ x ∈ l, a ≤ x) →
    l.Pairwise (fun u v => v ≤ u) → Inv2 (run ffChoice l) a := by
  induction l using List.reverseRecOn with
  | nil =>
    intro a _ _ _
    refine ⟨?_, ?_⟩
    · simp [run]
    · intro j j' hj hj'; simp [run] at hj'
  | append_singleton l y ih =>
    intro a ha hall hpw
    rw [List.pairwise_append] at hpw
    have hyl : ∀ x ∈ l, y ≤ x := fun x hx => hpw.2.2 x hx y (by simp)
    have hay : a ≤ y := hall y (by simp)
    have hy0 : 0 < y := lt_of_lt_of_le ha hay
    have hI := ih y hy0 hyl hpw.1
    rw [run_append]
    exact inv2_step _ y a hI hay hy0

theorem getD_lt' (P : List (List ℝ)) (j : ℕ) (hj : j < P.length) : P.getD j [] = P[j] := by
  simp [List.getD_eq_getElem?_getD, hj]

end BinPacking.Decreasing.FFBigs

open BinPacking.Decreasing BinPacking.Decreasing.FFBigs in
/-- D1: along a first-fit run on a nonincreasing positive list, every bin with level `≤ 2/3`
has level at most that of every earlier bin. -/
theorem ff_bigs_levels_antitone (S : List ℝ) (hS : S.Pairwise (fun a b => b ≤ a)) (hI : IsList S)
    (i j j' : ℕ) (hj : j < j') (hj' : j' < (run ffChoice (S.take i)).length)
    (hb : ((run ffChoice (S.take i)).getD j' []).sum ≤ 2 / 3) :
    ((run ffChoice (S.take i)).getD j' []).sum ≤ ((run ffChoice (S.take i)).getD j []).sum := by
  rw [getD_lt' _ _ hj'] at hb ⊢
  rw [getD_lt' _ _ (by omega)]
  have hpw : (S.take i).Pairwise (fun a b => b ≤ a) := hS.sublist (List.take_sublist _ _)
  rcases List.eq_nil_or_concat (S.take i) with h | ⟨l, y, hly⟩
  · rw [h] at hj'; simp [run] at hj'
  · have hmem : y ∈ S := List.mem_of_mem_take (by rw [hly]; simp)
    have hy0 : 0 < y := (hI y hmem).1
    have hall : ∀ x ∈ S.take i, y ≤ x := by
      intro x hx
      rw [hly, List.concat_eq_append] at hx hpw
      rw [List.pairwise_append] at hpw
      rcases List.mem_append.mp hx with hx | hx
      · exact hpw.2.2 x hx y (by simp)
      · simp at hx; rw [hx]
    have := inv2_run (S.take i) y hy0 hall hpw
    exact this.2 j j' hj hj' hb


namespace BinPacking.Decreasing.BfdFfdLarge

open BinPacking.Decreasing

/-- Invariant of the bins while only items `> 1/3` have been placed: bins are nonempty, all
items exceed `1/3` and are at least `a` (the next item), and singleton bins have nonincreasing
levels in index order. -/
def Inv (bins : List (List ℝ)) (a : ℝ) : Prop :=
  (∀ B ∈ bins, B ≠ [] ∧ ∀ x ∈ B, 1 / 3 < x ∧ a ≤ x) ∧
  (∀ (j j' : ℕ) (hj : j < j') (hj' : j' < bins.length),
    (bins[j]'(by omega)).length = 1 → bins[j'].length = 1 →
      bins[j'].sum ≤ (bins[j]'(by omega)).sum)

theorem findIdx_congr' {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, q x = true → p x = true) →
    (∀ (i : ℕ) (hi : i < l.length), p l[i] = true →
      (∀ (j : ℕ) (hj : j < i), p (l[j]'(by omega)) = false) → q l[i] = true) →
    l.findIdx q = l.findIdx p
  | [], _, _ => by simp
  | x :: t, h1, h2 => by
    rw [List.findIdx_cons, List.findIdx_cons]
    by_cases hp : p x = true
    · have hq : q x = true := h2 0 (by simp) (by simpa using hp) (fun j hj => by omega)
      simp [hp, hq]
    · have hq : q x = false := by
        cases hqx : q x
        · rfl
        · exact absurd (h1 x (by simp) hqx) hp
      have hp' : p x = false := by simpa using hp
      simp only [hp', hq, cond_false]
      congr 1
      apply findIdx_congr' p q t
      · intro y hy; exact h1 y (by simp [hy])
      · intro i hi hpi hj
        have := h2 (i + 1) (by simp; omega) (by simpa using hpi) (by
          intro j hj'
          rcases j with _ | j
          · simpa using hp'
          · simpa using hj j (by omega))
        simpa using this

theorem fit_single (bins : List (List ℝ)) (a : ℝ) (hI : Inv bins a) (ha : 1 / 3 < a)
    (B : List ℝ) (hB : B ∈ bins) (hfit : B.sum + a ≤ 1) : B.length = 1 := by
  obtain ⟨hne, hel⟩ := hI.1 B hB
  match B, hne, hel, hfit with
  | [x], _, _, _ => rfl
  | x :: y :: u, _, hel, hfit =>
    exfalso
    have hx := (hel x (by simp)).1
    have hy := (hel y (by simp)).1
    have hu : 0 ≤ u.sum := List.sum_nonneg (fun z hz => by
      have := (hel z (by simp [hz])).1; linarith)
    simp only [List.sum_cons] at hfit
    linarith

theorem choice_eq (bins : List (List ℝ)) (a : ℝ) (hI : Inv bins a) (ha : 1 / 3 < a) :
    bfChoice bins a = ffChoice bins a := by
  unfold bfChoice ffChoice
  apply findIdx_congr'
  · intro x _ hq
    simp only [decide_eq_true_eq] at hq ⊢
    exact hq.1
  · intro i hi hp hj
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hp hj ⊢
    refine ⟨hp, ?_⟩
    intro B' hB' hfit'
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hB'
    rcases lt_trichotomy m i with hmi | hmi | hmi
    · exact absurd hfit' (hj m hmi)
    · subst hmi; exact le_refl _
    · exact hI.2 i m hmi hm (fit_single bins a hI ha _ (List.getElem_mem _) hp)
        (fit_single bins a hI ha _ (List.getElem_mem _) hfit')

theorem inv_step (bins : List (List ℝ)) (y a : ℝ) (hI : Inv bins y) (hy : 1 / 3 < y)
    (hay : a ≤ y) : Inv (placeAt bins (ffChoice bins y) y) a := by
  obtain ⟨h1, h2⟩ := hI
  unfold placeAt
  split_ifs with hc
  · refine ⟨?_, ?_⟩
    · intro B hB
      obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hB
      simp only [List.getElem_mapIdx]
      have hm' : m < bins.length := by simpa using hm
      obtain ⟨hne, hel⟩ := h1 _ (List.getElem_mem hm')
      split_ifs
      · refine ⟨by simp, ?_⟩
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨(hel x hx).1, le_trans hay (hel x hx).2⟩
        · simp at hx; subst hx; exact ⟨hy, hay⟩
      · exact ⟨hne, fun x hx => ⟨(hel x hx).1, le_trans hay (hel x hx).2⟩⟩
    · intro j j' hj hj' hl hl'
      simp only [List.length_mapIdx] at hj'
      simp only [List.getElem_mapIdx] at hl hl' ⊢
      have hne : ∀ (k : ℕ) (hk : k < bins.length), (bins[k]).length ≠ 0 := by
        intro k hk h0
        exact (h1 _ (List.getElem_mem hk)).1 (List.eq_nil_of_length_eq_zero h0)
      split_ifs at hl hl' ⊢ with e1 e2 e2
      all_goals first
        | exact h2 j j' hj hj' hl hl'
        | omega
        | (have := hne j (by omega); simp only [List.length_append, List.length_singleton] at hl; omega)
        | (have := hne j' (by omega); simp only [List.length_append, List.length_singleton] at hl'; omega)
  · refine ⟨?_, ?_⟩
    · intro B hB
      rcases List.mem_append.mp hB with hB | hB
      · obtain ⟨hne, hel⟩ := h1 B hB
        exact ⟨hne, fun x hx => ⟨(hel x hx).1, le_trans hay (hel x hx).2⟩⟩
      · simp at hB; subst hB
        refine ⟨by simp, ?_⟩
        intro x hx; simp at hx; subst hx; exact ⟨hy, hay⟩
    · intro j j' hj hj' hl hl'
      simp only [List.length_append, List.length_singleton] at hj'
      by_cases hj'' : j' < bins.length
      · simp only [List.getElem_append_left hj'', List.getElem_append_left (show j < bins.length by omega)] at hl hl' ⊢
        exact h2 j j' hj hj'' hl hl'
      · have e : j' = bins.length := by omega
        subst e
        simp only [List.getElem_append_left (show j < bins.length by omega),
          List.getElem_append_right (le_refl _)] at hl ⊢
        simp only [Nat.sub_self, List.getElem_cons_zero, List.sum_singleton]
        obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl
        have hmem := (h1 _ (List.getElem_mem (show j < bins.length by omega))).2 x (by simp [hx])
        rw [hx, List.sum_singleton]
        exact hmem.2

theorem run_append (c : List (List ℝ) → ℝ → ℕ) (l : List ℝ) (y : ℝ) :
    run c (l ++ [y]) = placeAt (run c l) (c (run c l) y) y := by
  simp [run, List.foldl_append]

theorem main (l : List ℝ) : ∀ (a : ℝ), (∀ x ∈ l, 1 / 3 < x ∧ a ≤ x) →
    l.Pairwise (fun u v => v ≤ u) →
    run bfChoice l = run ffChoice l ∧ Inv (run ffChoice l) a := by
  induction l using List.reverseRecOn with
  | nil =>
    intro a _ _
    refine ⟨rfl, ?_, ?_⟩
    · simp [run]
    · intro j j' hj hj'; simp [run] at hj'
  | append_singleton l y ih =>
    intro a hall hpw
    rw [List.pairwise_append] at hpw
    have hyl : ∀ x ∈ l, 1 / 3 < x ∧ y ≤ x := fun x hx =>
      ⟨(hall x (by simp [hx])).1, hpw.2.2 x hx y (by simp)⟩
    obtain ⟨hr, hI⟩ := ih y hyl hpw.1
    have hy := hall y (by simp)
    have hc := choice_eq _ y hI hy.1
    refine ⟨?_, ?_⟩
    · rw [run_append, run_append, hr, hc]
    · rw [run_append]
      exact inv_step _ y a hI hy.1 hy.2

end BinPacking.Decreasing.BfdFfdLarge

namespace BinPacking.Decreasing.BfdFfdLarge

theorem core (S : List ℝ) (hpw : S.Pairwise (fun u v => v ≤ u)) (i : Fin S.length)
    (hi : (i : ℕ) < (S.filter (fun a => decide ((1 / 3 : ℝ) < a))).length) :
    binOf bfChoice S i = binOf ffChoice S i ∧ slotOf bfChoice S i = slotOf ffChoice S i := by
  have hsplit : S = S.take i ++ S[(i : ℕ)] :: S.drop ((i : ℕ) + 1) := by
    rw [← List.drop_eq_getElem_cons]; simp
  have hpw2 : (S.take i ++ S[(i : ℕ)] :: S.drop ((i : ℕ) + 1)).Pairwise (fun u v => v ≤ u) :=
    hsplit ▸ hpw
  rw [List.pairwise_append, List.pairwise_cons] at hpw2
  have hbig : 1 / 3 < S[(i : ℕ)] := by
    by_contra hle
    push Not at hle
    have hf : S.filter (fun a => decide ((1 / 3 : ℝ) < a)) =
        (S.take i).filter (fun a => decide ((1 / 3 : ℝ) < a)) ++
        (S[(i : ℕ)] :: S.drop ((i : ℕ) + 1)).filter (fun a => decide ((1 / 3 : ℝ) < a)) := by
      rw [← List.filter_append]; exact congrArg _ hsplit
    have hnil : (S[(i : ℕ)] :: S.drop ((i : ℕ) + 1)).filter
        (fun a => decide ((1 / 3 : ℝ) < a)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      simp only [decide_eq_true_eq, not_lt]
      rcases List.mem_cons.mp hx with hx | hx
      · rw [hx]; exact hle
      · exact le_trans (hpw2.2.1.1 x hx) hle
    rw [hf, hnil, List.append_nil] at hi
    have := List.length_filter_le (fun a => decide ((1 / 3 : ℝ) < a)) (S.take i)
    simp only [List.length_take] at this
    omega
  have hall : ∀ x ∈ S.take i, 1 / 3 < x ∧ S[(i : ℕ)] ≤ x := by
    intro x hx
    have := hpw2.2.2 x hx S[(i : ℕ)] (List.mem_cons.mpr (Or.inl rfl))
    exact ⟨lt_of_lt_of_le hbig this, this⟩
  obtain ⟨hr, hI⟩ := main (S.take i) S[(i : ℕ)] hall hpw2.1
  have hbin : binOf bfChoice S i = binOf ffChoice S i := by
    unfold binOf
    rw [hr, List.get_eq_getElem]
    exact choice_eq _ _ hI hbig
  refine ⟨hbin, ?_⟩
  unfold slotOf
  rw [hbin, hr]

end BinPacking.Decreasing.BfdFfdLarge

namespace BinPacking.Decreasing.Phase2

/-! Phase 2 of Theorem 3.4 (items in `[1/6, 1/3]`), augmented-bin model.
A bin remembers its free capacity `c0` at the start of phase 2, the list `s` of items it received
while its stream capacity `lv = c0 - s.sum` was at least `1/3` (stream items), and the list `g` of
items received afterwards (gap items). -/

/-- capacity-form first fit (same as the bridge file). -/
noncomputable def capFF (caps : List ℝ) (a : ℝ) : List ℝ :=
  let j := caps.findIdx (fun c => decide (a ≤ c))
  if j < caps.length then caps.modify j (fun c => c - a) else caps ++ [1 - a]

/-- capacity-form best fit (same as the bridge file). -/
noncomputable def capBF (caps : List ℝ) (a : ℝ) : List ℝ :=
  let j := caps.findIdx (fun c => decide (a ≤ c ∧ ∀ c' ∈ caps, a ≤ c' → c ≤ c'))
  if j < caps.length then caps.modify j (fun c => c - a) else caps ++ [1 - a]

structure Bin where
  c0 : ℝ
  s : List ℝ
  g : List ℝ

namespace Bin

def lv (b : Bin) : ℝ := b.c0 - b.s.sum

def cap (b : Bin) : ℝ := b.c0 - b.s.sum - b.g.sum

noncomputable def put (b : Bin) (a : ℝ) : Bin :=
  if 1 / 3 ≤ b.lv then ⟨b.c0, b.s ++ [a], b.g⟩ else ⟨b.c0, b.s, b.g ++ [a]⟩

theorem cap_put (b : Bin) (a : ℝ) : (b.put a).cap = b.cap - a := by
  unfold put cap lv
  split_ifs <;> simp [List.sum_append] <;> ring

end Bin

def newBin (a : ℝ) : Bin := ⟨1, [a], []⟩

noncomputable def stepF (bins : List Bin) (a : ℝ) : List Bin :=
  let j := bins.findIdx (fun b => decide (a ≤ b.cap))
  if j < bins.length then bins.modify j (fun b => b.put a) else bins ++ [newBin a]

noncomputable def stepB (bins : List Bin) (a : ℝ) : List Bin :=
  let j := bins.findIdx (fun b => decide (a ≤ b.cap ∧ ∀ b' ∈ bins, a ≤ b'.cap → b.cap ≤ b'.cap))
  if j < bins.length then bins.modify j (fun b => b.put a) else bins ++ [newBin a]

theorem map_modify_cap (bins : List Bin) (j : ℕ) (a : ℝ) :
    (bins.modify j (fun b => b.put a)).map Bin.cap =
      (bins.map Bin.cap).modify j (fun c => c - a) := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_map, List.getElem_modify]
    split_ifs <;> simp [Bin.cap_put]

theorem stepF_cap (bins : List Bin) (a : ℝ) :
    (stepF bins a).map Bin.cap = capFF (bins.map Bin.cap) a := by
  unfold stepF capFF
  dsimp only
  rw [List.findIdx_map, List.length_map]
  simp only [Function.comp_def]
  split_ifs with h
  · exact map_modify_cap _ _ _
  · simp [newBin, Bin.cap]

theorem stepB_cap (bins : List Bin) (a : ℝ) :
    (stepB bins a).map Bin.cap = capBF (bins.map Bin.cap) a := by
  unfold stepB capBF
  dsimp only
  have hidx : (bins.map Bin.cap).findIdx
      (fun c => decide (a ≤ c ∧ ∀ c' ∈ bins.map Bin.cap, a ≤ c' → c ≤ c')) =
      bins.findIdx (fun b => decide (a ≤ b.cap ∧ ∀ b' ∈ bins, a ≤ b'.cap → b.cap ≤ b'.cap)) := by
    rw [List.findIdx_map]
    congr 1
    funext b
    simp only [Function.comp, List.forall_mem_map]
  rw [hidx, List.length_map]
  split_ifs with h
  · exact map_modify_cap _ _ _
  · simp [newBin, Bin.cap]

theorem foldlF_cap (T : List ℝ) : ∀ bins : List Bin,
    (T.foldl stepF bins).map Bin.cap = T.foldl capFF (bins.map Bin.cap) := by
  induction T with
  | nil => intro bins; rfl
  | cons a t ih => intro bins; simp only [List.foldl_cons]; rw [ih, stepF_cap]

theorem foldlB_cap (T : List ℝ) : ∀ bins : List Bin,
    (T.foldl stepB bins).map Bin.cap = T.foldl capBF (bins.map Bin.cap) := by
  induction T with
  | nil => intro bins; rfl
  | cons a t ih => intro bins; simp only [List.foldl_cons]; rw [ih, stepB_cap]

/-- initial augmented bins from the phase-2 start capacities. -/
def init (C0 : List ℝ) : List Bin := C0.map (fun c => ⟨c, [], []⟩)

theorem init_cap (C0 : List ℝ) : (init C0).map Bin.cap = C0 := by
  simp [init, Bin.cap, Function.comp_def]

/-! ### Indexing helpers -/

def dflt : Bin := ⟨0, [], []⟩

noncomputable def nth (bins : List Bin) (j : ℕ) : Bin := bins.getD j dflt

theorem nth_eq (bins : List Bin) (j : ℕ) (h : j < bins.length) : nth bins j = bins[j] := by
  unfold nth; exact List.getD_eq_getElem bins dflt h

theorem nth_ge (bins : List Bin) (j : ℕ) (h : bins.length ≤ j) : nth bins j = dflt := by
  unfold nth; exact List.getD_eq_default bins dflt h

theorem nth_modify (bins : List Bin) (k : ℕ) (f : Bin → Bin) (j : ℕ) :
    nth (bins.modify k f) j = if j = k ∧ j < bins.length then f (nth bins j) else nth bins j := by
  by_cases hj : j < bins.length
  · have hj' : j < (bins.modify k f).length := by simpa using hj
    rw [nth_eq _ _ hj', nth_eq _ _ hj, List.getElem_modify]
    by_cases e : j = k
    · subst e; simp [hj]
    · rw [if_neg (fun h => e h.symm), if_neg (fun h => e h.1)]
  · have hj' : (bins.modify k f).length ≤ j := by simp; omega
    rw [nth_ge _ _ hj', nth_ge _ _ (by omega), if_neg (fun h => hj h.2)]

theorem nth_append (bins : List Bin) (b : Bin) (j : ℕ) :
    nth (bins ++ [b]) j =
      if j < bins.length then nth bins j else if j = bins.length then b else dflt := by
  by_cases hj : j < bins.length
  · rw [if_pos hj, nth_eq _ _ (by simp; omega), nth_eq _ _ hj, List.getElem_append_left hj]
  · rw [if_neg hj]
    by_cases e : j = bins.length
    · subst e; rw [if_pos rfl, nth_eq _ _ (by simp)]; simp
    · rw [if_neg e, nth_ge _ _ (by simp; omega)]

/-! ### Heads -/

/-- a bin is finished when its stream capacity dropped below `1/3`. -/
noncomputable def head (bins : List Bin) : ℕ := bins.findIdx (fun b => decide (1 / 3 ≤ b.lv))

theorem head_le (bins : List Bin) : head bins ≤ bins.length := List.findIdx_le_length

theorem lt_head (bins : List Bin) (j : ℕ) (h : j < head bins) : (nth bins j).lv < 1 / 3 := by
  have hl : j < bins.length := lt_of_lt_of_le h (head_le bins)
  have := List.not_of_lt_findIdx h
  rw [nth_eq _ _ hl]
  simpa using this

theorem head_unf (bins : List Bin) (h : head bins < bins.length) :
    1 / 3 ≤ (nth bins (head bins)).lv := by
  have := List.findIdx_getElem (w := h)
  rw [nth_eq _ _ h]
  unfold head
  simpa using this

theorem head_le_of (bins : List Bin) (j : ℕ) (hj : j < bins.length) (h : 1 / 3 ≤ (nth bins j).lv) :
    head bins ≤ j := by
  by_contra hc
  have := lt_head bins j (by omega)
  linarith

noncomputable def shead (bins : List Bin) (a : ℝ) : List Bin :=
  if head bins < bins.length then bins.modify (head bins) (fun b => b.put a) else bins ++ [newBin a]

/-! ### The two placement rules in head terms -/

theorem stepF_cases (bins : List Bin) (a : ℝ) (ha3 : a ≤ 1 / 3)
    (hg : ∀ j < bins.length, 1 / 3 ≤ (nth bins j).lv → (nth bins j).g = []) :
    (∃ k, k < bins.length ∧ (nth bins k).lv < 1 / 3 ∧ a ≤ (nth bins k).cap ∧
        stepF bins a = bins.modify k (fun b => b.put a)) ∨ stepF bins a = shead bins a := by
  unfold stepF
  dsimp only
  generalize hj : bins.findIdx (fun b => decide (a ≤ b.cap)) = j
  by_cases hjh : j < head bins
  · have hl : j < bins.length := lt_of_lt_of_le hjh (head_le _)
    left
    refine ⟨j, hl, lt_head _ _ hjh, ?_, by rw [if_pos hl]⟩
    have hl' : bins.findIdx (fun b => decide (a ≤ b.cap)) < bins.length := by rw [hj]; exact hl
    have := List.findIdx_getElem (w := hl')
    rw [nth_eq _ _ hl]
    simp only [hj, decide_eq_true_eq] at this
    exact this
  · right
    unfold shead
    by_cases hh : head bins < bins.length
    · have hu := head_unf bins hh
      have hgz := hg _ hh hu
      have hfit : a ≤ (nth bins (head bins)).cap := by
        unfold Bin.cap; rw [hgz]; unfold Bin.lv at hu; simp only [List.sum_nil, sub_zero]; linarith
      have hjle : j ≤ head bins := by
        by_contra hc
        push Not at hc
        have := List.not_of_lt_findIdx (p := fun b => decide (a ≤ b.cap)) (xs := bins)
          (i := head bins) (by rw [hj]; exact hc)
        rw [nth_eq _ _ hh] at hfit
        simp only [decide_eq_false_iff_not, not_le] at this
        linarith
      have hj_eq : j = head bins := le_antisymm hjle (not_lt.mp hjh)
      rw [if_pos hh, hj_eq, if_pos hh]
    · have hj_ge : bins.length ≤ j := le_trans (not_lt.mp hh) (not_lt.mp hjh)
      rw [if_neg hh, if_neg (by omega)]

theorem exists_tight (a : ℝ) : ∀ l : List Bin, (∃ b ∈ l, a ≤ b.cap) →
    ∃ b ∈ l, a ≤ b.cap ∧ ∀ b' ∈ l, a ≤ b'.cap → b.cap ≤ b'.cap
  | [], h => by simp at h
  | x :: t, h => by
    by_cases ht : ∃ b ∈ t, a ≤ b.cap
    · obtain ⟨b, hb, hfit, hmin⟩ := exists_tight a t ht
      by_cases hx : a ≤ x.cap ∧ x.cap ≤ b.cap
      · refine ⟨x, by simp, hx.1, ?_⟩
        intro b' hb' hf
        rcases List.mem_cons.mp hb' with e | e
        · rw [e]
        · exact le_trans hx.2 (hmin b' e hf)
      · refine ⟨b, by simp [hb], hfit, ?_⟩
        intro b' hb' hf
        rcases List.mem_cons.mp hb' with e | e
        · subst e; push Not at hx; exact le_of_lt (hx hf)
        · exact hmin b' e hf
    · obtain ⟨b, hb, hfit⟩ := h
      rcases List.mem_cons.mp hb with e | e
      · subst e
        refine ⟨b, by simp, hfit, ?_⟩
        intro b' hb' hf
        rcases List.mem_cons.mp hb' with e' | e'
        · rw [e']
        · exact absurd ⟨b', e', hf⟩ ht
      · exact absurd ⟨b, e, hfit⟩ ht

theorem stepB_cases (bins : List Bin) (a : ℝ) (ha3 : a ≤ 1 / 3)
    (hg : ∀ j < bins.length, 1 / 3 ≤ (nth bins j).lv → (nth bins j).g = [])
    (hgn : ∀ j < bins.length, 0 ≤ (nth bins j).g.sum)
    (hsort : ∀ i j, i < j → j < bins.length → 1 / 3 ≤ (nth bins i).lv → 1 / 3 ≤ (nth bins j).lv →
      (nth bins i).lv ≤ (nth bins j).lv) :
    (∃ k, k < bins.length ∧ (nth bins k).lv < 1 / 3 ∧ a ≤ (nth bins k).cap ∧
        stepB bins a = bins.modify k (fun b => b.put a)) ∨
      (stepB bins a = shead bins a ∧
        ∀ k < bins.length, (nth bins k).lv < 1 / 3 → (nth bins k).cap < a) := by
  have caple : ∀ j < bins.length, (nth bins j).cap ≤ (nth bins j).lv := by
    intro j hj; have := hgn j hj; unfold Bin.cap Bin.lv; linarith
  have capeq : ∀ j < bins.length, 1 / 3 ≤ (nth bins j).lv → (nth bins j).cap = (nth bins j).lv := by
    intro j hj hu; unfold Bin.cap Bin.lv; rw [hg j hj hu]; simp
  unfold stepB
  dsimp only
  by_cases hex : ∃ k, k < bins.length ∧ (nth bins k).lv < 1 / 3 ∧ a ≤ (nth bins k).cap
  · left
    obtain ⟨k, hk, hkf, hkfit⟩ := hex
    obtain ⟨b, hb, hbfit, hbmin⟩ := exists_tight a bins ⟨bins[k], List.getElem_mem hk, by
      rw [← nth_eq _ _ hk]; exact hkfit⟩
    have hlt : bins.findIdx (fun b => decide (a ≤ b.cap ∧ ∀ b' ∈ bins, a ≤ b'.cap → b.cap ≤ b'.cap))
        < bins.length := List.findIdx_lt_length.mpr ⟨b, hb, by simpa using ⟨hbfit, hbmin⟩⟩
    generalize hj : bins.findIdx
      (fun b => decide (a ≤ b.cap ∧ ∀ b' ∈ bins, a ≤ b'.cap → b.cap ≤ b'.cap)) = j at hlt
    have hpj := List.findIdx_getElem (w := (by rw [hj]; exact hlt :
      bins.findIdx (fun b => decide (a ≤ b.cap ∧ ∀ b' ∈ bins, a ≤ b'.cap → b.cap ≤ b'.cap)) <
        bins.length))
    simp only [hj, decide_eq_true_eq] at hpj
    obtain ⟨hjfit, hjmin⟩ := hpj
    have hjk : bins[j].cap ≤ (nth bins k).cap := by
      rw [nth_eq _ _ hk]; exact hjmin _ (List.getElem_mem hk) (by rw [← nth_eq _ _ hk]; exact hkfit)
    have hjfin : (nth bins j).lv < 1 / 3 := by
      by_contra hc
      push Not at hc
      have e := capeq j hlt hc
      rw [nth_eq _ _ hlt] at e hc
      have := caple k hk
      linarith
    refine ⟨j, hlt, hjfin, by rw [nth_eq _ _ hlt]; exact hjfit, by rw [if_pos hlt]⟩
  · right
    push Not at hex
    refine ⟨?_, fun k hk hkf => hex k hk hkf⟩
    unfold shead
    by_cases hh : head bins < bins.length
    · have hu := head_unf bins hh
      have hidx : bins.findIdx
          (fun b => decide (a ≤ b.cap ∧ ∀ b' ∈ bins, a ≤ b'.cap → b.cap ≤ b'.cap)) = head bins := by
        rw [List.findIdx_eq hh]
        constructor
        · simp only [decide_eq_true_eq]
          rw [← nth_eq _ _ hh]
          refine ⟨by rw [capeq _ hh hu]; linarith, ?_⟩
          intro b' hb' hf
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb'
          rw [← nth_eq _ _ hi] at hf ⊢
          have hiu : 1 / 3 ≤ (nth bins i).lv := by
            by_contra hc; push Not at hc; have := hex i hi hc; linarith
          have hle := head_le_of bins i hi hiu
          rw [capeq _ hh hu, capeq _ hi hiu]
          rcases lt_or_eq_of_le hle with h1 | h1
          · exact hsort _ _ h1 hi hu hiu
          · rw [h1]
        · intro i hi
          simp only [decide_eq_false_iff_not, not_and]
          intro hf
          have hil : i < bins.length := lt_trans hi hh
          have := hex i hil (lt_head bins i hi)
          rw [nth_eq _ _ hil] at this
          linarith
      rw [hidx, if_pos hh]
    · have hall : ∀ b ∈ bins,
          (fun b => decide (a ≤ b.cap ∧ ∀ b' ∈ bins, a ≤ b'.cap → b.cap ≤ b'.cap)) b = false := by
        intro b hb
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
        simp only [decide_eq_false_iff_not, not_and]
        intro hf
        have := hex i hi (lt_head bins i (by omega))
        rw [nth_eq _ _ hi] at this
        linarith
      rw [List.findIdx_eq_length_of_false hall, if_neg (lt_irrefl _), if_neg hh]

/-! ### Single-run invariant -/

theorem put_unf (b : Bin) (a : ℝ) (h : 1 / 3 ≤ b.lv) : b.put a = ⟨b.c0, b.s ++ [a], b.g⟩ := by
  unfold Bin.put; rw [if_pos h]

theorem put_fin (b : Bin) (a : ℝ) (h : b.lv < 1 / 3) : b.put a = ⟨b.c0, b.s, b.g ++ [a]⟩ := by
  unfold Bin.put; rw [if_neg (not_le.mpr h)]

theorem head_map (bins : List Bin) :
    head bins = (bins.map Bin.lv).findIdx (fun c => decide (1 / 3 ≤ c)) := by
  unfold head; rw [List.findIdx_map]; rfl

structure RInv (C0 : List ℝ) (bins : List Bin) (a : ℝ) : Prop where
  len : C0.length ≤ bins.length
  c0 : ∀ j < bins.length, (nth bins j).c0 = if j < C0.length then C0.getD j 0 else 1
  spos : ∀ j < bins.length, ∀ x ∈ (nth bins j).s, a ≤ x
  gform : ∀ j < bins.length, (nth bins j).g = [] ∨
    ∃ x, (nth bins j).g = [x] ∧ a ≤ x ∧ x ≤ (nth bins j).lv ∧ (nth bins j).lv < 1 / 3
  stream : ∀ j < bins.length, ∀ k < (nth bins j).s.length,
    1 / 3 ≤ (nth bins j).c0 - ((nth bins j).s.take k).sum
  after : ∀ j, head bins < j → j < bins.length → (nth bins j).s = []
  new : ∀ j, C0.length ≤ j → j < bins.length → (nth bins j).s ≠ []
  six : head bins < bins.length → bins.length = C0.length ∨ bins.length = head bins + 1

def Sorted (bins : List Bin) : Prop :=
  ∀ i j, i < j → j < bins.length → 1 / 3 ≤ (nth bins i).lv → 1 / 3 ≤ (nth bins j).lv →
    (nth bins i).lv ≤ (nth bins j).lv

theorem RInv.g_nil_of_unf {C0 : List ℝ} {bins : List Bin} {a : ℝ} (R : RInv C0 bins a) (j : ℕ)
    (hj : j < bins.length) (h : 1 / 3 ≤ (nth bins j).lv) : (nth bins j).g = [] := by
  rcases R.gform j hj with e | ⟨x, _, _, _, hl⟩
  · exact e
  · linarith

theorem RInv.g_nil_of_fit {C0 : List ℝ} {bins : List Bin} {a : ℝ} (R : RInv C0 bins a)
    (ha : 1 / 6 ≤ a) (j : ℕ) (hj : j < bins.length) (h : a ≤ (nth bins j).cap) :
    (nth bins j).g = [] := by
  rcases R.gform j hj with e | ⟨x, e, hx1, hx2, hl⟩
  · exact e
  · exfalso
    unfold Bin.cap at h
    unfold Bin.lv at hl
    rw [e] at h
    simp only [List.sum_cons, List.sum_nil, add_zero] at h
    linarith

theorem RInv.gsum_nonneg {C0 : List ℝ} {bins : List Bin} {a : ℝ} (R : RInv C0 bins a) (ha : 0 ≤ a)
    (j : ℕ) (hj : j < bins.length) : 0 ≤ (nth bins j).g.sum := by
  rcases R.gform j hj with e | ⟨x, e, hx1, _, _⟩
  · rw [e]; simp
  · rw [e]; simp only [List.sum_cons, List.sum_nil, add_zero]; linarith

theorem RInv.mono {C0 : List ℝ} {bins : List Bin} {a : ℝ} (R : RInv C0 bins a) (a' : ℝ)
    (h : a' ≤ a) : RInv C0 bins a' where
  len := R.len
  c0 := R.c0
  spos := fun j hj x hx => le_trans h (R.spos j hj x hx)
  gform := fun j hj => by
    rcases R.gform j hj with e | ⟨x, e, h1, h2, h3⟩
    · exact Or.inl e
    · exact Or.inr ⟨x, e, le_trans h h1, h2, h3⟩
  stream := R.stream
  after := R.after
  new := R.new
  six := R.six

theorem nth_init (C0 : List ℝ) (j : ℕ) (hj : j < C0.length) :
    nth (init C0) j = ⟨C0.getD j 0, [], []⟩ := by
  rw [nth_eq _ _ (by simpa [init] using hj)]
  simp [init, List.getElem?_eq_getElem hj]

theorem RInv_init (C0 : List ℝ) (a : ℝ) : RInv C0 (init C0) a where
  len := by simp [init]
  c0 := fun j hj => by
    have hj' : j < C0.length := by simpa [init] using hj
    rw [nth_init _ _ hj', if_pos hj']
  spos := fun j hj x hx => by
    have hj' : j < C0.length := by simpa [init] using hj
    rw [nth_init _ _ hj'] at hx; simp at hx
  gform := fun j hj => by
    have hj' : j < C0.length := by simpa [init] using hj
    left; rw [nth_init _ _ hj']
  stream := fun j hj k hk => by
    have hj' : j < C0.length := by simpa [init] using hj
    rw [nth_init _ _ hj'] at hk; simp at hk
  after := fun j _ hj => by
    have hj' : j < C0.length := by simpa [init] using hj
    rw [nth_init _ _ hj']
  new := fun j h1 h2 => by simp [init] at h2; omega
  six := fun _ => Or.inl (by simp [init])

theorem Sorted_init (C0 : List ℝ)
    (hC : ∀ i j, i < j → j < C0.length → 1 / 3 ≤ C0.getD i 0 → 1 / 3 ≤ C0.getD j 0 →
      C0.getD i 0 ≤ C0.getD j 0) : Sorted (init C0) := by
  intro i j hij hj hi' hj'
  have hjl : j < C0.length := by simpa [init] using hj
  have hil : i < C0.length := by omega
  rw [nth_init _ _ hil] at hi' ⊢
  rw [nth_init _ _ hjl] at hj' ⊢
  unfold Bin.lv at hi' hj' ⊢
  simp only [List.sum_nil, sub_zero] at hi' hj' ⊢
  exact hC i j hij hjl hi' hj'

/-- the G-move (an item into a finished bin that fits it). -/
theorem nth_G (bins : List Bin) (a : ℝ) (k : ℕ) (hk : k < bins.length)
    (hkf : (nth bins k).lv < 1 / 3) (hg0 : (nth bins k).g = []) (j : ℕ) :
    nth (bins.modify k (fun b => b.put a)) j =
      if j = k then ⟨(nth bins k).c0, (nth bins k).s, [a]⟩ else nth bins j := by
  rw [nth_modify]
  by_cases e : j = k
  · subst e; rw [if_pos ⟨rfl, hk⟩, if_pos rfl, put_fin _ _ hkf, hg0]; rfl
  · rw [if_neg (fun h => e h.1), if_neg e]

theorem lv_G (bins : List Bin) (a : ℝ) (k : ℕ) (hk : k < bins.length)
    (hkf : (nth bins k).lv < 1 / 3) (hg0 : (nth bins k).g = []) (j : ℕ) :
    (nth (bins.modify k (fun b => b.put a)) j).lv = (nth bins j).lv := by
  rw [nth_G bins a k hk hkf hg0]
  split_ifs with e
  · subst e; rfl
  · rfl

theorem head_G (bins : List Bin) (a : ℝ) (k : ℕ) (hk : k < bins.length)
    (hkf : (nth bins k).lv < 1 / 3) (hg0 : (nth bins k).g = []) :
    head (bins.modify k (fun b => b.put a)) = head bins := by
  rw [head_map, head_map]
  congr 1
  apply List.ext_getElem (by simp)
  intro n h1 h2
  have h2' : n < bins.length := by simpa using h2
  have h1' : n < (bins.modify k (fun b => b.put a)).length := by simpa using h1
  simp only [List.getElem_map]
  rw [← nth_eq _ _ h1', ← nth_eq _ _ h2', lv_G bins a k hk hkf hg0]

theorem RInv.G {C0 : List ℝ} {bins : List Bin} {a : ℝ} (R : RInv C0 bins a) (ha : 1 / 6 ≤ a)
    (k : ℕ) (hk : k < bins.length) (hkf : (nth bins k).lv < 1 / 3)
    (hfit : a ≤ (nth bins k).cap) : RInv C0 (bins.modify k (fun b => b.put a)) a := by
  have hg0 := R.g_nil_of_fit ha k hk hfit
  have hlen : (bins.modify k (fun b => b.put a)).length = bins.length := List.length_modify ..
  have hhead := head_G bins a k hk hkf hg0
  have hnth := nth_G bins a k hk hkf hg0
  constructor
  · rw [hlen]; exact R.len
  · intro j hj; rw [hlen] at hj; rw [hnth]; by_cases e : j = k
    · subst e; rw [if_pos rfl]; exact R.c0 _ hj
    · rw [if_neg e]; exact R.c0 j hj
  · intro j hj; rw [hlen] at hj; rw [hnth]; by_cases e : j = k
    · subst e; rw [if_pos rfl]; exact R.spos _ hj
    · rw [if_neg e]; exact R.spos j hj
  · intro j hj; rw [hlen] at hj; rw [hnth]; by_cases e : j = k
    · subst e; rw [if_pos rfl]
      right
      refine ⟨a, rfl, le_refl a, ?_, hkf⟩
      have : (nth bins j).cap = (nth bins j).lv := by
        unfold Bin.cap Bin.lv; rw [hg0]; simp
      show a ≤ (nth bins j).lv
      linarith
    · rw [if_neg e]; exact R.gform j hj
  · intro j hj; rw [hlen] at hj; rw [hnth]; by_cases e : j = k
    · subst e; rw [if_pos rfl]; exact R.stream _ hj
    · rw [if_neg e]; exact R.stream j hj
  · intro j hj1 hj2; rw [hlen] at hj2; rw [hhead] at hj1; rw [hnth]; by_cases e : j = k
    · subst e; rw [if_pos rfl]; exact R.after _ hj1 hj2
    · rw [if_neg e]; exact R.after j hj1 hj2
  · intro j hj1 hj2; rw [hlen] at hj2; rw [hnth]; by_cases e : j = k
    · subst e; rw [if_pos rfl]; exact R.new _ hj1 hj2
    · rw [if_neg e]; exact R.new j hj1 hj2
  · rw [hhead, hlen]; exact R.six

theorem Sorted.G {bins : List Bin} (S : Sorted bins) (a : ℝ) (k : ℕ) (hk : k < bins.length)
    (hkf : (nth bins k).lv < 1 / 3) (hg0 : (nth bins k).g = []) :
    Sorted (bins.modify k (fun b => b.put a)) := by
  intro i j hij hj hi' hj'
  have hj2 : j < bins.length := by simpa using hj
  simp only [lv_G bins a k hk hkf hg0] at hi' hj' ⊢
  exact S i j hij hj2 hi' hj'

/-! ### The S-move (an item into the head, or a new bin) -/

theorem nth_Sm (bins : List Bin) (a : ℝ) (hh : head bins < bins.length)
    (hg0 : (nth bins (head bins)).g = []) (j : ℕ) :
    nth (bins.modify (head bins) (fun b => b.put a)) j =
      if j = head bins then ⟨(nth bins (head bins)).c0, (nth bins (head bins)).s ++ [a], []⟩
      else nth bins j := by
  rw [nth_modify]
  by_cases e : j = head bins
  · rw [if_pos ⟨e, e ▸ hh⟩, if_pos e, e, put_unf _ _ (head_unf bins hh), hg0]
  · rw [if_neg (fun h => e h.1), if_neg e]

theorem head_Sm_ge (bins : List Bin) (a : ℝ) (hh : head bins < bins.length)
    (hg0 : (nth bins (head bins)).g = []) :
    head bins ≤ head (bins.modify (head bins) (fun b => b.put a)) := by
  by_contra hlt
  push Not at hlt
  have hl : head (bins.modify (head bins) (fun b => b.put a)) <
      (bins.modify (head bins) (fun b => b.put a)).length := by simp; omega
  have hu := head_unf _ hl
  rw [nth_Sm bins a hh hg0, if_neg (by omega)] at hu
  have := lt_head bins _ hlt
  linarith

theorem nth_new (bins : List Bin) (a : ℝ) (j : ℕ) :
    nth (bins ++ [newBin a]) j =
      if j < bins.length then nth bins j else if j = bins.length then newBin a else dflt :=
  nth_append bins (newBin a) j

theorem head_new (bins : List Bin) (a : ℝ) (ha3 : a ≤ 1 / 3) (hh : head bins = bins.length) :
    head (bins ++ [newBin a]) = bins.length := by
  apply le_antisymm
  · apply head_le_of _ _ (by simp)
    rw [nth_new, if_neg (lt_irrefl _), if_pos rfl]
    unfold newBin Bin.lv; simp; linarith
  · by_contra hlt
    push Not at hlt
    have hl : head (bins ++ [newBin a]) < (bins ++ [newBin a]).length := by simp; omega
    have hu := head_unf _ hl
    rw [nth_new, if_pos hlt] at hu
    have := lt_head bins (head (bins ++ [newBin a])) (by rw [hh]; exact hlt)
    linarith

theorem RInv.S {C0 : List ℝ} {bins : List Bin} {a : ℝ} (R : RInv C0 bins a)
    (ha3 : a ≤ 1 / 3) : RInv C0 (shead bins a) a := by
  unfold shead
  by_cases hh : head bins < bins.length
  · rw [if_pos hh]
    have hu := head_unf bins hh
    have hg0 := R.g_nil_of_unf _ hh hu
    have hlen : (bins.modify (head bins) (fun b => b.put a)).length = bins.length :=
      List.length_modify ..
    have hge := head_Sm_ge bins a hh hg0
    have hnth := nth_Sm bins a hh hg0
    constructor
    · rw [hlen]; exact R.len
    · intro j hj; rw [hlen] at hj; rw [hnth]; by_cases e : j = head bins
      · rw [if_pos e]; rw [e] at hj ⊢; exact R.c0 _ hj
      · rw [if_neg e]; exact R.c0 j hj
    · intro j hj; rw [hlen] at hj; rw [hnth]; by_cases e : j = head bins
      · rw [if_pos e]; intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · rw [e] at hj; exact R.spos _ hj x hx
        · simp at hx; rw [hx]
      · rw [if_neg e]; exact R.spos j hj
    · intro j hj; rw [hlen] at hj; rw [hnth]; by_cases e : j = head bins
      · rw [if_pos e]; left; rfl
      · rw [if_neg e]; exact R.gform j hj
    · intro j hj; rw [hlen] at hj; rw [hnth]; by_cases e : j = head bins
      · rw [if_pos e]
        intro k hk
        simp only [List.length_append, List.length_singleton] at hk
        show 1 / 3 ≤ (nth bins (head bins)).c0 -
          (((nth bins (head bins)).s ++ [a]).take k).sum
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
        · rw [List.take_append_of_le_length (le_of_lt hk')]
          exact R.stream _ hh k hk'
        · rw [hk', List.take_append_of_le_length (le_refl _), List.take_length]
          unfold Bin.lv at hu; linarith
      · rw [if_neg e]; exact R.stream j hj
    · intro j hj1 hj2; rw [hlen] at hj2
      have e : j ≠ head bins := by omega
      rw [hnth, if_neg e]
      exact R.after j (by omega) hj2
    · intro j hj1 hj2; rw [hlen] at hj2; rw [hnth]; by_cases e : j = head bins
      · rw [if_pos e]; simp
      · rw [if_neg e]; exact R.new j hj1 hj2
    · intro hh'
      rw [hlen] at hh' ⊢
      rcases R.six hh with e | e
      · exact Or.inl e
      · right; omega
  · rw [if_neg hh]
    have hh2 : head bins = bins.length := le_antisymm (head_le bins) (not_lt.mp hh)
    have hhd := head_new bins a ha3 hh2
    have hlen : (bins ++ [newBin a]).length = bins.length + 1 := by simp
    constructor
    · rw [hlen]; have := R.len; omega
    · intro j hj; rw [hlen] at hj; rw [nth_new]
      by_cases e : j < bins.length
      · rw [if_pos e]; exact R.c0 j e
      · have e2 : j = bins.length := by omega
        rw [if_neg e, if_pos e2]
        have := R.len
        rw [if_neg (by omega)]; rfl
    · intro j hj; rw [hlen] at hj; rw [nth_new]
      by_cases e : j < bins.length
      · rw [if_pos e]; exact R.spos j e
      · rw [if_neg e, if_pos (by omega)]; intro x hx; simp [newBin] at hx; rw [hx]
    · intro j hj; rw [hlen] at hj; rw [nth_new]
      by_cases e : j < bins.length
      · rw [if_pos e]; exact R.gform j e
      · rw [if_neg e, if_pos (by omega)]; left; rfl
    · intro j hj; rw [hlen] at hj; rw [nth_new]
      by_cases e : j < bins.length
      · rw [if_pos e]; exact R.stream j e
      · rw [if_neg e, if_pos (by omega)]; intro k hk
        simp [newBin] at hk; subst hk; simp [newBin]; norm_num
    · intro j hj1 hj2; rw [hlen] at hj2; rw [hhd] at hj1; omega
    · intro j hj1 hj2; rw [hlen] at hj2; rw [nth_new]
      by_cases e : j < bins.length
      · rw [if_pos e]; exact R.new j hj1 e
      · rw [if_neg e, if_pos (by omega)]; simp [newBin]
    · intro _; right; rw [hhd, hlen]

theorem Sorted.S {C0 : List ℝ} {bins : List Bin} {a : ℝ} (S : Sorted bins) (R : RInv C0 bins a)
    (ha : 0 ≤ a) (ha3 : a ≤ 1 / 3) : Sorted (shead bins a) := by
  unfold shead
  by_cases hh : head bins < bins.length
  · rw [if_pos hh]
    have hu := head_unf bins hh
    have hg0 := R.g_nil_of_unf _ hh hu
    have hnth := nth_Sm bins a hh hg0
    intro i j hij hj hi' hj'
    have hj2 : j < bins.length := by simpa using hj
    simp only [hnth] at hi' hj' ⊢
    by_cases ei : i = head bins
    · have ej : j ≠ head bins := by omega
      rw [if_pos ei] at hi' ⊢
      rw [if_neg ej] at hj' ⊢
      have := S _ _ (by omega) hj2 hu hj'
      unfold Bin.lv at this ⊢
      simp only [List.sum_append, List.sum_cons, List.sum_nil, add_zero]
      linarith
    · rw [if_neg ei] at hi' ⊢
      by_cases ej : j = head bins
      · exfalso
        have := lt_head bins i (by omega)
        linarith
      · rw [if_neg ej] at hj' ⊢
        exact S i j hij hj2 hi' hj'
  · rw [if_neg hh]
    have hh2 : head bins = bins.length := le_antisymm (head_le bins) (not_lt.mp hh)
    intro i j hij hj hi' hj'
    have hi2 : i < bins.length := by simp at hj; omega
    rw [nth_new, if_pos hi2] at hi'
    have := lt_head bins i (by omega)
    linarith

/-! ### Joint invariant -/

/-- `l1` is pointwise at most the prefix of `l2` of the same length. -/
def PW (l1 l2 : List ℝ) : Prop :=
  l1.length ≤ l2.length ∧ ∀ k (h1 : k < l1.length) (h2 : k < l2.length), l1[k] ≤ l2[k]

/-- number of phase-2 items in a bin. -/
def sig (b : Bin) : ℕ := b.s.length + b.g.length

/-- the per-bin joint condition (`bB` best fit, `bF` first fit, `inF` : the first-fit bin exists). -/
def KP (bB bF : Bin) (inF : Prop) : Prop :=
  (bB.lv < 1 / 3 → inF ∧ bF.lv < 1 / 3 ∧
      (bF.s.length < bB.s.length ∨ (bF.s.length = bB.s.length ∧ bF.lv ≤ bB.lv))) ∧
  (1 / 3 ≤ bB.lv → PW bB.s bF.s ∨ (inF ∧ bF.lv < 1 / 3 ∧ bF.s.length < bB.s.length))

structure KInv (B F : List Bin) : Prop where
  tot : (B.map sig).sum = (F.map sig).sum
  kp : ∀ j < B.length, KP (nth B j) (nth F j) (j < F.length)

theorem KInv_init (C0 : List ℝ) : KInv (init C0) (init C0) where
  tot := rfl
  kp := fun j hj => by
    constructor
    · intro h; exact ⟨hj, h, Or.inr ⟨rfl, le_refl _⟩⟩
    · intro _; left; exact ⟨le_refl _, fun k h1 h2 => le_refl _⟩

theorem KInv.heads {B F : List Bin} (K : KInv B F) : head B ≤ head F := by
  by_contra hc
  push Not at hc
  have hlB : head F < B.length := lt_of_lt_of_le hc (head_le B)
  have hfin := lt_head B (head F) hc
  obtain ⟨hlF, hfF, _⟩ := (K.kp _ hlB).1 hfin
  have := head_unf F hlF
  linarith

theorem sum_le_of_le (l1 : List ℕ) : ∀ l2 : List ℕ, l1.length ≤ l2.length →
    (∀ j (h1 : j < l1.length) (h2 : j < l2.length), l1[j] ≤ l2[j]) → l1.sum ≤ l2.sum := by
  induction l1 with
  | nil => intro l2 _ _; simp
  | cons x t ih =>
    intro l2 hlen hle
    match l2, hlen, hle with
    | y :: u, hlen, hle =>
      simp only [List.sum_cons]
      have hxy : x ≤ y := hle 0 (by simp) (by simp)
      have := ih u (by simp at hlen; omega) (fun j h1 h2 => by
        have := hle (j + 1) (by simp; omega) (by simp; omega)
        simpa using this)
      omega

theorem sum_lt_of_le (l1 : List ℕ) : ∀ l2 : List ℕ, l1.length ≤ l2.length →
    (∀ j (h1 : j < l1.length) (h2 : j < l2.length), l1[j] ≤ l2[j]) →
    (∃ j, ∃ (h1 : j < l1.length) (h2 : j < l2.length), l1[j] < l2[j]) → l1.sum < l2.sum := by
  induction l1 with
  | nil => intro l2 _ _ h; obtain ⟨j, h1, _⟩ := h; simp at h1
  | cons x t ih =>
    intro l2 hlen hle hlt
    match l2, hlen, hle, hlt with
    | y :: u, hlen, hle, hlt =>
      simp only [List.sum_cons]
      have hxy : x ≤ y := hle 0 (by simp) (by simp)
      have hle' : ∀ j (h1 : j < t.length) (h2 : j < u.length), t[j] ≤ u[j] := fun j h1 h2 => by
        have := hle (j + 1) (by simp; omega) (by simp; omega)
        simpa using this
      have hlen' : t.length ≤ u.length := by simp at hlen; omega
      obtain ⟨j, h1, h2, hj⟩ := hlt
      rcases j with _ | j
      · have := sum_le_of_le t u hlen' hle'
        simp at hj
        omega
      · have := ih u hlen' hle' ⟨j, by simp at h1; omega, by simp at h2; omega, by simpa using hj⟩
        omega

theorem count_contra {C0 : List ℝ} {B F : List Bin} {a : ℝ} (ha6 : 1 / 6 ≤ a)
    (RB : RInv C0 B a) (RF : RInv C0 F a) (K : KInv B F)
    (hnofit : ∀ k < B.length, (nth B k).lv < 1 / 3 → (nth B k).cap < a)
    (hlen : F.length ≤ B.length)
    (hunf : ∀ j < F.length, 1 / 3 ≤ (nth B j).lv → sig (nth F j) ≤ sig (nth B j))
    (k0 : ℕ) (hk0 : k0 < F.length) (hk0F : (nth F k0).lv < 1 / 3) (hk0fit : a ≤ (nth F k0).cap)
    (hk0B : (nth B k0).lv < 1 / 3) : False := by
  have hper : ∀ j < F.length, (nth B j).lv < 1 / 3 →
      sig (nth F j) + (if j = k0 then 1 else 0) ≤ sig (nth B j) := by
    intro j hj hfB
    have hjB : j < B.length := lt_of_lt_of_le hj hlen
    obtain ⟨_, hfF, hcmp⟩ := (K.kp j hjB).1 hfB
    have hgB : a ≤ (nth B j).lv → 1 ≤ (nth B j).g.length := by
      intro hl
      rcases RB.gform j hjB with e | ⟨x, e, _, _, _⟩
      · exfalso
        have := hnofit j hjB hfB
        unfold Bin.cap at this
        unfold Bin.lv at hl
        rw [e] at this
        simp only [List.sum_nil, sub_zero] at this
        linarith
      · rw [e]; simp
    have hgF : (nth F j).g.length ≤ (if a ≤ (nth F j).lv then 1 else 0) := by
      rcases RF.gform j hj with e | ⟨x, e, hx1, hx2, _⟩
      · rw [e]; simp
      · rw [e, if_pos (le_trans hx1 hx2)]; simp
    unfold sig
    by_cases e : j = k0
    · rw [if_pos e]
      subst e
      have hg0 := RF.g_nil_of_fit ha6 _ hk0 hk0fit
      have hlvF : a ≤ (nth F j).lv := by
        unfold Bin.cap at hk0fit; rw [hg0] at hk0fit; unfold Bin.lv
        simpa using hk0fit
      rw [hg0]
      simp only [List.length_nil, add_zero]
      rcases hcmp with hc | ⟨hc1, hc2⟩
      · omega
      · have := hgB (le_trans hlvF hc2); omega
    · rw [if_neg e]
      by_cases hl : a ≤ (nth F j).lv
      · rw [if_pos hl] at hgF
        rcases hcmp with hc | ⟨hc1, hc2⟩
        · omega
        · have := hgB (le_trans hl hc2); omega
      · rw [if_neg hl] at hgF
        rcases hcmp with hc | ⟨hc1, hc2⟩ <;> omega
  have key : (F.map sig).sum < (B.map sig).sum := by
    apply sum_lt_of_le
    · simpa using hlen
    · intro j h1 h2
      simp only [List.getElem_map]
      have hj : j < F.length := by simpa using h1
      have hjB : j < B.length := by simpa using h2
      rw [← nth_eq _ _ hj, ← nth_eq _ _ hjB]
      by_cases hfB : (nth B j).lv < 1 / 3
      · have := hper j hj hfB; omega
      · exact hunf j hj (not_lt.mp hfB)
    · refine ⟨k0, by simpa using hk0, by simpa using lt_of_lt_of_le hk0 hlen, ?_⟩
      simp only [List.getElem_map]
      rw [← nth_eq _ _ hk0, ← nth_eq _ _ (lt_of_lt_of_le hk0 hlen)]
      have := hper k0 hk0 hk0B
      rw [if_pos rfl] at this
      omega
  rw [K.tot] at key
  exact lt_irrefl _ key

/-! ### Pointwise-prefix facts -/

theorem PW_nil (l : List ℝ) : PW [] l := ⟨by simp, fun k h1 _ => by simp at h1⟩

theorem PW_append_right {l1 l2 : List ℝ} (h : PW l1 l2) (x : ℝ) : PW l1 (l2 ++ [x]) := by
  refine ⟨by simp; have := h.1; omega, fun k h1 h2 => ?_⟩
  have hk : k < l2.length := lt_of_lt_of_le h1 h.1
  rw [List.getElem_append_left hk]
  exact h.2 k h1 hk

theorem PW_snoc {l1 l2 : List ℝ} (h : PW l1 l2) (x : ℝ) (hlt : l1.length < l2.length)
    (hx : x ≤ l2[l1.length]) : PW (l1 ++ [x]) l2 := by
  refine ⟨by simp; omega, fun k h1 h2 => ?_⟩
  simp only [List.length_append, List.length_singleton] at h1
  rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with hk | hk
  · rw [List.getElem_append_left hk]; exact h.2 k hk h2
  · subst hk
    rw [List.getElem_append_right (le_refl _)]
    simpa using hx

theorem PW_snoc_both {l1 l2 : List ℝ} (h : PW l1 l2) (x : ℝ) (hx : ∀ y ∈ l2, x ≤ y) :
    PW (l1 ++ [x]) (l2 ++ [x]) := by
  refine ⟨by simp; exact h.1, fun k h1 h2 => ?_⟩
  simp only [List.length_append, List.length_singleton] at h1
  rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with hk | hk
  · rw [List.getElem_append_left hk, List.getElem_append_left (lt_of_lt_of_le hk h.1)]
    exact h.2 k hk _
  · subst hk
    rw [List.getElem_append_right (le_refl _)]
    by_cases hl : l1.length < l2.length
    · rw [List.getElem_append_left hl]
      simpa using hx _ (List.getElem_mem hl)
    · have : l1.length = l2.length := le_antisymm h.1 (not_lt.mp hl)
      rw [List.getElem_append_right (by omega)]
      simp [this]

theorem PW_sum : ∀ (l1 l2 : List ℝ), PW l1 l2 → l1.sum ≤ (l2.take l1.length).sum
  | [], _, _ => by simp
  | x :: t, [], h => by have := h.1; simp at this
  | x :: t, y :: u, h => by
    simp only [List.sum_cons, List.length_cons, List.take_succ_cons]
    have hxy : x ≤ y := h.2 0 (by simp) (by simp)
    have := PW_sum t u ⟨by have := h.1; simp at this; omega, fun k h1 h2 => by
      have := h.2 (k + 1) (by simp; omega) (by simp; omega)
      simpa using this⟩
    linarith

theorem sum_take_le (l : List ℝ) (hpos : ∀ x ∈ l, 0 ≤ x) (n : ℕ) : (l.take n).sum ≤ l.sum := by
  conv_rhs => rw [← List.take_append_drop n l]
  rw [List.sum_append]
  have : 0 ≤ (l.drop n).sum := List.sum_nonneg (fun x hx => hpos x (List.mem_of_mem_drop hx))
  linarith

/-- if the best-fit stream list is pointwise below the first-fit one and the best-fit bin is
finished, then both stream lists have the same length and first fit has no more room. -/
theorem fin_of_PW (c0 : ℝ) (sB sF : List ℝ) (h : PW sB sF) (hpos : ∀ x ∈ sF, 0 ≤ x)
    (hstream : ∀ k < sF.length, 1 / 3 ≤ c0 - (sF.take k).sum) (hfin : c0 - sB.sum < 1 / 3) :
    sF.length = sB.length ∧ c0 - sF.sum ≤ c0 - sB.sum := by
  have hs := PW_sum sB sF h
  have hlen : sF.length = sB.length := by
    by_contra hne
    have hlt : sB.length < sF.length := lt_of_le_of_ne h.1 (Ne.symm hne)
    have := hstream _ hlt
    linarith
  refine ⟨hlen, ?_⟩
  have : sF.take sB.length = sF := by rw [← hlen]; exact List.take_length
  rw [this] at hs
  linarith

/-! ### Per-bin transfer lemmas for the joint invariant -/

theorem KP_mono {bB bF : Bin} {P Q : Prop} (hK : KP bB bF P) (h : P → Q) : KP bB bF Q :=
  ⟨fun hf => by obtain ⟨p, q, r⟩ := hK.1 hf; exact ⟨h p, q, r⟩,
   fun hu => by rcases hK.2 hu with e | ⟨p, q, r⟩; exact Or.inl e; exact Or.inr ⟨h p, q, r⟩⟩

theorem KP_congr {bB bF bB' bF' : Bin} {P Q : Prop} (hK : KP bB bF P)
    (hBs : bB'.s = bB.s) (hBl : bB'.lv = bB.lv) (hFs : bF'.s = bF.s) (hFl : bF'.lv = bF.lv)
    (h : P → Q) : KP bB' bF' Q := by
  have := KP_mono hK h
  unfold KP at this ⊢
  rw [hBs, hBl, hFs, hFl]
  exact this

/-- first fit adds a stream item, best fit's bin is untouched. -/
theorem KP_UB_SF {bB bF : Bin} {P Q : Prop} (a : ℝ) (hK : KP bB bF P) (hFu : 1 / 3 ≤ bF.lv)
    (h : P → Q) : KP bB ⟨bF.c0, bF.s ++ [a], bF.g⟩ Q := by
  constructor
  · intro hf
    obtain ⟨_, hfF, _⟩ := hK.1 hf
    linarith
  · intro hu
    rcases hK.2 hu with e | ⟨_, hfF, _⟩
    · exact Or.inl (PW_append_right e a)
    · linarith

/-- best fit adds a stream item to an unfinished bin, first fit's bin is untouched. -/
theorem KP_SB_UF {bB bF : Bin} {P : Prop} (a : ℝ) (hK : KP bB bF P) (hBu : 1 / 3 ≤ bB.lv)
    (hc0 : bB.c0 = bF.c0) (hFa : ∀ x ∈ bF.s, a ≤ x) (ha : 0 < a)
    (hFst : ∀ k < bF.s.length, 1 / 3 ≤ bF.c0 - (bF.s.take k).sum)
    (hP : bB.s.length < bF.s.length → P)
    (hnc : bB.s.length = bF.s.length → P ∧ bF.lv < 1 / 3) :
    KP ⟨bB.c0, bB.s ++ [a], []⟩ bF P := by
  have hpos : ∀ x ∈ bF.s, 0 ≤ x := fun x hx => le_trans (le_of_lt ha) (hFa x hx)
  rcases hK.2 hBu with hpw | ⟨p, hfF, hlt⟩
  · rcases lt_or_eq_of_le hpw.1 with hlt | heq
    · have hpw' : PW (bB.s ++ [a]) bF.s := PW_snoc hpw a hlt (hFa _ (List.getElem_mem hlt))
      constructor
      · intro hf
        have hf' : bF.c0 - (bB.s ++ [a]).sum < 1 / 3 := by
          rw [← hc0]; exact hf
        obtain ⟨e1, e2⟩ := fin_of_PW bF.c0 _ _ hpw' hpos hFst hf'
        refine ⟨hP hlt, ?_, Or.inr ⟨e1, ?_⟩⟩
        · show bF.c0 - bF.s.sum < 1 / 3
          linarith
        · show bF.c0 - bF.s.sum ≤ bB.c0 - (bB.s ++ [a]).sum
          rw [hc0]; exact e2
      · intro _; exact Or.inl hpw'
    · obtain ⟨p, hfF⟩ := hnc heq
      constructor
      · intro _
        refine ⟨p, hfF, Or.inl ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega
      · intro _
        refine Or.inr ⟨p, hfF, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega
  · constructor
    · intro _
      refine ⟨p, hfF, Or.inl ?_⟩
      simp only [List.length_append, List.length_singleton]
      omega
    · intro _
      refine Or.inr ⟨p, hfF, ?_⟩
      simp only [List.length_append, List.length_singleton]
      omega

/-- both rules add the item to the same (shared head) bin. -/
theorem KP_SB_SF {bB bF : Bin} {P Q : Prop} (a : ℝ) (hK : KP bB bF P) (hBu : 1 / 3 ≤ bB.lv)
    (hFu : 1 / 3 ≤ bF.lv) (hc0 : bB.c0 = bF.c0) (hFa : ∀ x ∈ bF.s, a ≤ x) (ha : 0 < a)
    (hFst : ∀ k < (bF.s ++ [a]).length, 1 / 3 ≤ bF.c0 - ((bF.s ++ [a]).take k).sum)
    (hQ : Q) : KP ⟨bB.c0, bB.s ++ [a], []⟩ ⟨bF.c0, bF.s ++ [a], bF.g⟩ Q := by
  have hpw : PW bB.s bF.s := by
    rcases hK.2 hBu with e | ⟨_, hfF, _⟩
    · exact e
    · exfalso; linarith
  have hpw' := PW_snoc_both hpw a hFa
  have hpos : ∀ x ∈ bF.s ++ [a], 0 ≤ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact le_trans (le_of_lt ha) (hFa x hx)
    · simp at hx; rw [hx]; exact le_of_lt ha
  constructor
  · intro hf
    have hf' : bF.c0 - (bB.s ++ [a]).sum < 1 / 3 := by rw [← hc0]; exact hf
    obtain ⟨e1, e2⟩ := fin_of_PW bF.c0 _ _ hpw' hpos hFst hf'
    refine ⟨hQ, ?_, Or.inr ⟨e1, ?_⟩⟩
    · show bF.c0 - (bF.s ++ [a]).sum < 1 / 3
      linarith
    · show bF.c0 - (bF.s ++ [a]).sum ≤ bB.c0 - (bB.s ++ [a]).sum
      rw [hc0]; exact e2
  · intro _; exact Or.inl hpw'

/-- best fit opens a new bin. -/
theorem KP_NB {bF : Bin} {Q : Prop} (a : ℝ) (ha3 : a ≤ 1 / 3) (h : PW [a] bF.s) :
    KP (newBin a) bF Q := by
  constructor
  · intro hf; exfalso; unfold newBin Bin.lv at hf; simp at hf; linarith
  · intro _; exact Or.inl h

theorem PW_single (a : ℝ) (l : List ℝ) (hne : l ≠ []) (ha : ∀ x ∈ l, a ≤ x) : PW [a] l := by
  have hl : 0 < l.length := List.length_pos_of_ne_nil hne
  have := PW_snoc (PW_nil l) a hl (ha _ (List.getElem_mem hl))
  simpa using this

/-! ### Move shapes and the joint step -/

theorem sig_put (b : Bin) (a : ℝ) : sig (b.put a) = sig b + 1 := by
  unfold Bin.put sig; split_ifs <;> simp <;> omega

theorem sum_sig_modify (a : ℝ) : ∀ (l : List Bin) (k : ℕ), k < l.length →
    ((l.modify k (fun b => b.put a)).map sig).sum = (l.map sig).sum + 1
  | [], k, h => by simp at h
  | x :: t, 0, _ => by
    simp only [List.modify_zero_cons, List.map_cons, List.sum_cons, sig_put]; omega
  | x :: t, k + 1, h => by
    simp only [List.modify_succ_cons, List.map_cons, List.sum_cons]
    rw [sum_sig_modify a t k (by simp at h; omega)]; omega

theorem sum_sig_shead (l : List Bin) (a : ℝ) :
    ((shead l a).map sig).sum = (l.map sig).sum + 1 := by
  unfold shead; split_ifs with h
  · exact sum_sig_modify a l _ h
  · simp [sig, newBin]

theorem desc_G (X : List Bin) (a : ℝ) (k : ℕ) (hk : k < X.length) (hkf : (nth X k).lv < 1 / 3)
    (hg0 : (nth X k).g = []) :
    (X.modify k (fun b => b.put a)).length = X.length ∧
      ∀ j, (nth (X.modify k (fun b => b.put a)) j).s = (nth X j).s ∧
        (nth (X.modify k (fun b => b.put a)) j).lv = (nth X j).lv := by
  refine ⟨List.length_modify .., fun j => ?_⟩
  rw [nth_G X a k hk hkf hg0]
  split_ifs with e
  · subst e; exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem desc_S (X : List Bin) (a : ℝ) (hh : head X < X.length) (hg0 : (nth X (head X)).g = []) :
    (shead X a).length = X.length ∧ (∀ j, j ≠ head X → nth (shead X a) j = nth X j) ∧
      nth (shead X a) (head X) = ⟨(nth X (head X)).c0, (nth X (head X)).s ++ [a], []⟩ := by
  unfold shead; rw [if_pos hh]
  refine ⟨List.length_modify .., fun j hj => ?_, ?_⟩
  · rw [nth_Sm X a hh hg0, if_neg hj]
  · rw [nth_Sm X a hh hg0, if_pos rfl]

theorem desc_N (X : List Bin) (a : ℝ) (hh : ¬ head X < X.length) :
    (shead X a).length = X.length + 1 ∧ (∀ j, j ≠ X.length → nth (shead X a) j = nth X j) ∧
      nth (shead X a) X.length = newBin a := by
  unfold shead; rw [if_neg hh]
  refine ⟨by simp, fun j hj => ?_, ?_⟩
  · rw [nth_new]
    by_cases h1 : j < X.length
    · rw [if_pos h1]
    · rw [if_neg h1, if_neg hj, nth_ge _ _ (by omega)]
  · rw [nth_new, if_neg (lt_irrefl _), if_pos rfl]

theorem c0_eq {C0 : List ℝ} {B F : List Bin} {a a' : ℝ} (RB : RInv C0 B a) (RF : RInv C0 F a')
    (j : ℕ) (h1 : j < B.length) (h2 : j < F.length) : (nth B j).c0 = (nth F j).c0 := by
  rw [RB.c0 j h1, RF.c0 j h2]

theorem KInv.unf_lt {C0 : List ℝ} {B F : List Bin} {a : ℝ} (RB : RInv C0 B a) (RF : RInv C0 F a)
    (K : KInv B F) (j : ℕ) (hj : j < B.length) (hu : 1 / 3 ≤ (nth B j).lv) : j < F.length := by
  by_contra hc
  push Not at hc
  rcases (K.kp j hj).2 hu with hpw | ⟨hin, _, _⟩
  · have hF : (nth F j).s = [] := by rw [nth_ge _ _ hc]; rfl
    rw [hF] at hpw
    have hnil : (nth B j).s = [] := by simpa using hpw.1
    exact RB.new j (by have := RF.len; omega) hj hnil
  · omega

theorem KInv.len_le {C0 : List ℝ} {B F : List Bin} {a : ℝ} (RB : RInv C0 B a) (RF : RInv C0 F a)
    (K : KInv B F) : B.length ≤ F.length := by
  by_contra hc
  push Not at hc
  by_cases hu : 1 / 3 ≤ (nth B F.length).lv
  · have := K.unf_lt RB RF F.length hc hu; omega
  · have := ((K.kp F.length hc).1 (not_le.mp hu)).1; omega

theorem KInv.step {C0 : List ℝ} {B F : List Bin} {a : ℝ} (ha6 : 1 / 6 ≤ a) (ha3 : a ≤ 1 / 3)
    (RB : RInv C0 B a) (RF : RInv C0 F a) (K : KInv B F) (B' F' : List Bin)
    (RF' : RInv C0 F' a)
    (hB : (∃ k, k < B.length ∧ (nth B k).lv < 1 / 3 ∧ a ≤ (nth B k).cap ∧
        B' = B.modify k (fun b => b.put a)) ∨
      (B' = shead B a ∧ ∀ k < B.length, (nth B k).lv < 1 / 3 → (nth B k).cap < a))
    (hF : (∃ k, k < F.length ∧ (nth F k).lv < 1 / 3 ∧ a ≤ (nth F k).cap ∧
        F' = F.modify k (fun b => b.put a)) ∨ F' = shead F a) :
    KInv B' F' := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hlenBF := K.len_le RB RF
  have hheads := K.heads
  constructor
  · have e1 : (B'.map sig).sum = (B.map sig).sum + 1 := by
      rcases hB with ⟨k, hk, _, _, rfl⟩ | ⟨rfl, _⟩
      · exact sum_sig_modify a B k hk
      · exact sum_sig_shead B a
    have e2 : (F'.map sig).sum = (F.map sig).sum + 1 := by
      rcases hF with ⟨k, hk, _, _, rfl⟩ | rfl
      · exact sum_sig_modify a F k hk
      · exact sum_sig_shead F a
    rw [e1, e2, K.tot]
  have hFd : (F'.length = F.length ∧
        (∀ j, (nth F' j).s = (nth F j).s ∧ (nth F' j).lv = (nth F j).lv) ∧
        ∃ k0, k0 < F.length ∧ (nth F k0).lv < 1 / 3 ∧ a ≤ (nth F k0).cap) ∨
      (head F < F.length ∧ F'.length = F.length ∧ (∀ j, j ≠ head F → nth F' j = nth F j) ∧
        nth F' (head F) = ⟨(nth F (head F)).c0, (nth F (head F)).s ++ [a], []⟩) ∨
      (head F = F.length ∧ F'.length = F.length + 1 ∧ (∀ j, j ≠ F.length → nth F' j = nth F j) ∧
        nth F' F.length = newBin a) := by
    rcases hF with ⟨k, hk, hkf, hkfit, rfl⟩ | rfl
    · left
      obtain ⟨h1, h2⟩ := desc_G F a k hk hkf (RF.g_nil_of_fit ha6 k hk hkfit)
      exact ⟨h1, h2, k, hk, hkf, hkfit⟩
    · right
      by_cases hh : head F < F.length
      · left
        exact ⟨hh, desc_S F a hh (RF.g_nil_of_unf _ hh (head_unf F hh))⟩
      · right
        exact ⟨le_antisymm (head_le F) (not_lt.mp hh), desc_N F a hh⟩
  intro j hj
  rcases hB with ⟨k, hk, hkf, hkfit, rfl⟩ | ⟨rfl, hnofit⟩
  · -- best fit: G-move (views unchanged)
    obtain ⟨hBlen, hBv⟩ := desc_G B a k hk hkf (RB.g_nil_of_fit ha6 k hk hkfit)
    rw [hBlen] at hj
    have hK := K.kp j hj
    rcases hFd with ⟨hFlen, hFv, _⟩ | ⟨hh, hFlen, hFo, hFh⟩ | ⟨hh, hFlen, hFo, hFn⟩
    · exact KP_congr hK (hBv j).1 (hBv j).2 (hFv j).1 (hFv j).2 (by rw [hFlen]; exact id)
    · by_cases e : j = head F
      · subst e
        have h1 := KP_UB_SF (Q := head F < F'.length) a hK (head_unf F hh)
          (by rw [hFlen]; exact id)
        exact KP_congr h1 (hBv _).1 (hBv _).2 (by rw [hFh]) (by rw [hFh]; rfl) id
      · exact KP_congr hK (hBv j).1 (hBv j).2 (by rw [hFo j e]) (by rw [hFo j e])
          (by rw [hFlen]; exact id)
    · have e : j ≠ F.length := by omega
      exact KP_congr hK (hBv j).1 (hBv j).2 (by rw [hFo j e]) (by rw [hFo j e])
        (by rw [hFlen]; omega)
  · by_cases hhB : head B < B.length
    · -- best fit: S-move into its head
      obtain ⟨hBlen, hBo, hBh⟩ := desc_S B a hhB (RB.g_nil_of_unf _ hhB (head_unf B hhB))
      rw [hBlen] at hj
      have hK := K.kp j hj
      by_cases ej : j = head B
      · subst ej
        have hBu := head_unf B hhB
        have hjF := K.unf_lt RB RF _ hhB hBu
        have hc0 := c0_eq RB RF _ hhB hjF
        rcases hFd with ⟨hFlen, hFv, k0, hk0, hk0f, hk0fit⟩ | ⟨hh, hFlen, hFo, hFh⟩ |
            ⟨hh, hFlen, hFo, hFn⟩
        · have h1 := KP_SB_UF a hK hBu hc0 (RF.spos _ hjF) ha0 (RF.stream _ hjF) (fun _ => hjF) (by
            intro heq
            refine ⟨hjF, ?_⟩
            by_contra hFu
            push Not at hFu
            have hFhead : head F = head B := le_antisymm (head_le_of F _ hjF hFu) hheads
            have hlen : F.length ≤ B.length := by
              by_contra hc
              push Not at hc
              have h1 := RF.new B.length RB.len hc
              have h2 := RF.after B.length (by rw [hFhead]; exact hhB) hc
              exact h1 h2
            refine count_contra ha6 RB RF K hnofit hlen ?_ k0 hk0 hk0f hk0fit ?_
            · intro i hi hu
              have hiB : i < B.length := lt_of_lt_of_le hi hlen
              have hge : head B ≤ i := head_le_of B i hiB hu
              rcases eq_or_lt_of_le hge with e | e
              · subst e
                unfold sig
                rw [RB.g_nil_of_unf _ hiB hu, RF.g_nil_of_unf _ hi hFu]
                simp only [List.length_nil, add_zero]
                omega
              · have hsB := RB.after i e hiB
                have hsF := RF.after i (by rw [hFhead]; exact e) hi
                have hci := c0_eq RB RF i hiB hi
                have hlvF : 1 / 3 ≤ (nth F i).lv := by
                  unfold Bin.lv at hu ⊢; rw [hsB] at hu; rw [hsF, ← hci]; exact hu
                unfold sig
                rw [hsF, RF.g_nil_of_unf _ hi hlvF]
                simp
            · by_contra hu
              push Not at hu
              have hk0B : k0 < B.length := lt_of_lt_of_le hk0 hlen
              have hge : head B ≤ k0 := head_le_of B k0 hk0B hu
              rcases eq_or_lt_of_le hge with e | e
              · rw [← e] at hk0f; linarith
              · have hsB := RB.after k0 e hk0B
                have hsF := RF.after k0 (by rw [hFhead]; exact e) hk0
                have hci := c0_eq RB RF k0 hk0B hk0
                unfold Bin.lv at hu hk0f
                rw [hsB] at hu; rw [hsF, ← hci] at hk0f
                linarith)
          exact KP_congr h1 (by rw [hBh]) (by rw [hBh]) (hFv _).1 (hFv _).2
            (by rw [hFlen]; exact id)
        · by_cases eh : head F = head B
          · have hFu := head_unf F hh
            rw [eh] at hFu hFh hh
            have hst : ∀ k < ((nth F (head B)).s ++ [a]).length,
                1 / 3 ≤ (nth F (head B)).c0 - (((nth F (head B)).s ++ [a]).take k).sum := by
              have := RF'.stream (head B) (by rw [hFlen]; exact hh)
              rw [hFh] at this
              exact this
            have h1 := KP_SB_SF (Q := head B < F'.length) a hK hBu hFu hc0 (RF.spos _ hjF) ha0 hst
              (by rw [hFlen]; exact hjF)
            exact KP_congr h1 (by rw [hBh]) (by rw [hBh]) (by rw [hFh]) (by rw [hFh]; rfl) id
          · have hlt : head B < head F := lt_of_le_of_ne hheads (Ne.symm eh)
            have hFf := lt_head F _ hlt
            have h1 := KP_SB_UF a hK hBu hc0 (RF.spos _ hjF) ha0 (RF.stream _ hjF) (fun _ => hjF)
              (fun _ => ⟨hjF, hFf⟩)
            have hne : head B ≠ head F := fun h => eh h.symm
            exact KP_congr h1 (by rw [hBh]) (by rw [hBh]) (by rw [hFo _ hne]) (by rw [hFo _ hne])
              (by rw [hFlen]; exact id)
        · have hlt : head B < head F := by rw [hh]; exact hjF
          have hFf := lt_head F _ hlt
          have hne : head B ≠ F.length := by omega
          have h1 := KP_SB_UF a hK hBu hc0 (RF.spos _ hjF) ha0 (RF.stream _ hjF) (fun _ => hjF)
            (fun _ => ⟨hjF, hFf⟩)
          exact KP_congr h1 (by rw [hBh]) (by rw [hBh]) (by rw [hFo _ hne]) (by rw [hFo _ hne])
            (by rw [hFlen]; omega)
      · rcases hFd with ⟨hFlen, hFv, _⟩ | ⟨hh, hFlen, hFo, hFh⟩ | ⟨hh, hFlen, hFo, hFn⟩
        · exact KP_congr hK (by rw [hBo j ej]) (by rw [hBo j ej]) (hFv j).1 (hFv j).2
            (by rw [hFlen]; exact id)
        · by_cases e : j = head F
          · subst e
            have h1 := KP_UB_SF (Q := head F < F'.length) a hK (head_unf F hh)
              (by rw [hFlen]; exact id)
            exact KP_congr h1 (by rw [hBo _ ej]) (by rw [hBo _ ej]) (by rw [hFh]) (by rw [hFh]; rfl) id
          · exact KP_congr hK (by rw [hBo j ej]) (by rw [hBo j ej]) (by rw [hFo j e])
              (by rw [hFo j e]) (by rw [hFlen]; exact id)
        · have e : j ≠ F.length := by omega
          exact KP_congr hK (by rw [hBo j ej]) (by rw [hBo j ej]) (by rw [hFo j e]) (by rw [hFo j e])
            (by rw [hFlen]; omega)
    · -- best fit opens a new bin
      have hhB2 : head B = B.length := le_antisymm (head_le B) (not_lt.mp hhB)
      obtain ⟨hBlen, hBo, hBn⟩ := desc_N B a hhB
      rw [hBlen] at hj
      by_cases ej : j < B.length
      · have hK := K.kp j ej
        have ej' : j ≠ B.length := by omega
        rcases hFd with ⟨hFlen, hFv, _⟩ | ⟨hh, hFlen, hFo, hFh⟩ | ⟨hh, hFlen, hFo, hFn⟩
        · exact KP_congr hK (by rw [hBo j ej']) (by rw [hBo j ej']) (hFv j).1 (hFv j).2
            (by rw [hFlen]; exact id)
        · have e : j ≠ head F := by omega
          exact KP_congr hK (by rw [hBo j ej']) (by rw [hBo j ej']) (by rw [hFo j e])
            (by rw [hFo j e]) (by rw [hFlen]; exact id)
        · have e : j ≠ F.length := by omega
          exact KP_congr hK (by rw [hBo j ej']) (by rw [hBo j ej']) (by rw [hFo j e])
            (by rw [hFo j e]) (by rw [hFlen]; omega)
      · have ej2 : j = B.length := by omega
        subst ej2
        rw [hBn]
        apply KP_NB a ha3
        rcases hFd with ⟨hFlen, hFv, k0, hk0, hk0f, hk0fit⟩ | ⟨hh, hFlen, hFo, hFh⟩ |
            ⟨hh, hFlen, hFo, hFn⟩
        · rw [(hFv _).1]
          by_cases hlt : B.length < F.length
          · exact PW_single a _ (RF.new _ RB.len hlt) (RF.spos _ hlt)
          · exfalso
            exact count_contra ha6 RB RF K hnofit (by omega)
              (fun i hi hu => absurd hu (not_le.mpr (lt_head B i (by omega)))) k0 hk0 hk0f hk0fit
              (lt_head B k0 (by omega))
        · by_cases eh : head F = B.length
          · rw [← eh, hFh]
            exact PW_single a _ (by simp) (fun x hx => by
              rcases List.mem_append.mp hx with hx | hx
              · exact RF.spos _ hh x hx
              · simp at hx; rw [hx])
          · have hlt : B.length < head F := lt_of_le_of_ne (hhB2 ▸ hheads) (Ne.symm eh)
            have hne : B.length ≠ head F := by omega
            rw [hFo _ hne]
            exact PW_single a _ (RF.new _ RB.len (lt_trans hlt hh)) (RF.spos _ (lt_trans hlt hh))
        · by_cases eh : F.length = B.length
          · rw [← eh, hFn]
            exact PW_single a _ (by simp [newBin]) (by simp [newBin])
          · have hlt : B.length < F.length := lt_of_le_of_ne hlenBF (Ne.symm eh)
            have hne : B.length ≠ F.length := by omega
            rw [hFo _ hne]
            exact PW_single a _ (RF.new _ RB.len hlt) (RF.spos _ hlt)

/-! ### Phase 2 theorem -/

theorem run_le (C0 : List ℝ) : ∀ (T : List ℝ) (B F : List Bin) (u : ℝ),
    (∀ x ∈ T, 1 / 6 ≤ x ∧ x ≤ u ∧ x ≤ 1 / 3) → T.Pairwise (fun p q => q ≤ p) →
    RInv C0 B u → RInv C0 F u → Sorted B → KInv B F →
    (T.foldl stepB B).length ≤ (T.foldl stepF F).length
  | [], B, F, u, _, _, RB, RF, _, K => by simpa using K.len_le RB RF
  | x :: t, B, F, u, hT, hpw, RB0, RF0, SB, K => by
    obtain ⟨hx6, hxu, hx3⟩ := hT x (by simp)
    have RB := RB0.mono x hxu
    have RF := RF0.mono x hxu
    have hxpos : (0 : ℝ) ≤ x := by linarith
    -- first fit move
    have hF := stepF_cases F x hx3 (fun j hj hu => RF.g_nil_of_unf j hj hu)
    have hB := stepB_cases B x hx3 (fun j hj hu => RB.g_nil_of_unf j hj hu)
      (fun j hj => RB.gsum_nonneg hxpos j hj) SB
    have RF' : RInv C0 (stepF F x) x := by
      rcases hF with ⟨k, hk, hkf, hkfit, e⟩ | e
      · rw [e]; exact RF.G hx6 k hk hkf hkfit
      · rw [e]; exact RF.S hx3
    have RB' : RInv C0 (stepB B x) x := by
      rcases hB with ⟨k, hk, hkf, hkfit, e⟩ | ⟨e, _⟩
      · rw [e]; exact RB.G hx6 k hk hkf hkfit
      · rw [e]; exact RB.S hx3
    have SB' : Sorted (stepB B x) := by
      rcases hB with ⟨k, hk, hkf, hkfit, e⟩ | ⟨e, _⟩
      · rw [e]; exact SB.G x k hk hkf (RB.g_nil_of_fit hx6 k hk hkfit)
      · rw [e]; exact SB.S RB hxpos hx3
    have K' : KInv (stepB B x) (stepF F x) := by
      refine K.step hx6 hx3 RB RF (stepB B x) (stepF F x) RF' ?_ ?_
      · rcases hB with ⟨k, hk, hkf, hkfit, e⟩ | ⟨e, hn⟩
        · exact Or.inl ⟨k, hk, hkf, hkfit, e⟩
        · exact Or.inr ⟨e, hn⟩
      · rcases hF with ⟨k, hk, hkf, hkfit, e⟩ | e
        · exact Or.inl ⟨k, hk, hkf, hkfit, e⟩
        · exact Or.inr e
    have hT' : ∀ y ∈ t, 1 / 6 ≤ y ∧ y ≤ x ∧ y ≤ 1 / 3 := by
      intro y hy
      obtain ⟨h1, _, h3⟩ := hT y (by simp [hy])
      exact ⟨h1, (List.pairwise_cons.mp hpw).1 y hy, h3⟩
    simp only [List.foldl_cons]
    exact run_le C0 t _ _ x hT' (List.pairwise_cons.mp hpw).2 RB' RF' SB' K'

/-- PHASE 2: from equal phase-2 start capacities whose big entries (`≥ 1/3`) are nondecreasing in
index, best fit uses no more bins than first fit on any nonincreasing list in `[1/6, 1/3]`. -/
theorem phase2 (C0 : List ℝ)
    (hC : ∀ i j, i < j → j < C0.length → 1 / 3 ≤ C0.getD i 0 → 1 / 3 ≤ C0.getD j 0 →
      C0.getD i 0 ≤ C0.getD j 0)
    (T : List ℝ) (hT : ∀ x ∈ T, 1 / 6 ≤ x ∧ x ≤ 1 / 3) (hpw : T.Pairwise (fun p q => q ≤ p)) :
    (T.foldl capBF C0).length ≤ (T.foldl capFF C0).length := by
  have h := run_le C0 T (init C0) (init C0) (1 / 3)
    (fun x hx => ⟨(hT x hx).1, (hT x hx).2, (hT x hx).2⟩) hpw (RInv_init C0 _) (RInv_init C0 _)
    (Sorted_init C0 hC) (KInv_init C0)
  have e1 := foldlB_cap T (init C0)
  have e2 := foldlF_cap T (init C0)
  rw [init_cap] at e1 e2
  rw [← e1, ← e2, List.length_map, List.length_map]
  exact h

end BinPacking.Decreasing.Phase2


namespace BinPacking.Decreasing.Glue

open BinPacking.Decreasing

theorem capFF_eq : Phase2.capFF = CapModel.capFF := rfl

theorem capBF_eq : Phase2.capBF = CapModel.capBF := rfl

theorem sortDesc_pw (L : List ℝ) : (sortDesc L).Pairwise (fun u v => v ≤ u) := by
  have := List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
    (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; linarith)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _) L
  simp only [decide_eq_true_eq] at this
  exact this

theorem mem_sortDesc (L : List ℝ) (x : ℝ) (h : x ∈ sortDesc L) : x ∈ L := by
  unfold sortDesc at h
  exact (List.mergeSort_perm L _).mem_iff.mp h

theorem dropWhile_le (S : List ℝ) (hpw : S.Pairwise (fun u v => v ≤ u)) :
    ∀ x ∈ S.dropWhile (fun a => decide ((1 / 3 : ℝ) < a)), x ≤ 1 / 3 := by
  have hpw2 : (S.dropWhile (fun a => decide ((1 / 3 : ℝ) < a))).Pairwise (fun u v => v ≤ u) :=
    hpw.sublist (List.dropWhile_sublist _)
  intro x hx
  cases hD : S.dropWhile (fun a => decide ((1 / 3 : ℝ) < a)) with
  | nil => rw [hD] at hx; simp at hx
  | cons y r =>
    have hhd := List.head_dropWhile_not (fun a => decide ((1 / 3 : ℝ) < a)) (l := S)
      (by rw [hD]; simp)
    simp only [hD, List.head_cons, decide_eq_false_iff_not, not_lt] at hhd
    rw [hD] at hx hpw2
    rcases List.mem_cons.mp hx with e | e
    · rw [e]; exact hhd
    · exact le_trans ((List.pairwise_cons.mp hpw2).1 x e) hhd

theorem bfd_le_ffd_main (L : List ℝ) (hL : IsList L) (h6 : ∀ a ∈ L, (1 / 6 : ℝ) ≤ a) :
    BFD L ≤ FFD L := by
  have hpw := sortDesc_pw L
  have hmem : ∀ x ∈ sortDesc L, x ∈ L := fun x hx => mem_sortDesc L x hx
  have hsplit : sortDesc L = (sortDesc L).takeWhile (fun a => decide ((1 / 3 : ℝ) < a)) ++
      (sortDesc L).dropWhile (fun a => decide ((1 / 3 : ℝ) < a)) :=
    (List.takeWhile_append_dropWhile).symm
  generalize hS1 : (sortDesc L).takeWhile (fun a => decide ((1 / 3 : ℝ) < a)) = S1 at hsplit
  generalize hS2 : (sortDesc L).dropWhile (fun a => decide ((1 / 3 : ℝ) < a)) = S2 at hsplit
  have hS1big : ∀ x ∈ S1, 1 / 3 < x := by
    intro x hx
    rw [← hS1] at hx
    have := List.mem_takeWhile_imp hx
    simpa using this
  have hS1mem : ∀ x ∈ S1, x ∈ L := fun x hx => hmem x (by rw [hsplit]; exact List.mem_append_left _ hx)
  have hS2mem : ∀ x ∈ S2, x ∈ L := fun x hx => hmem x (by rw [hsplit]; exact List.mem_append_right _ hx)
  have hS12pw : (S1 ++ S2).Pairwise (fun u v => v ≤ u) := by rw [← hsplit]; exact hpw
  have hS1pw : S1.Pairwise (fun u v => v ≤ u) := hS12pw.sublist (List.sublist_append_left _ _)
  have hS2pw : S2.Pairwise (fun u v => v ≤ u) := hS12pw.sublist (List.sublist_append_right _ _)
  have hS2le : ∀ x ∈ S2, x ≤ 1 / 3 := by
    intro x hx
    rw [← hS2] at hx
    exact dropWhile_le _ hpw x hx
  have hK1 := (BfdFfdLarge.main S1 0 (fun x hx => ⟨hS1big x hx, by linarith [hS1big x hx]⟩)
    hS1pw).1
  have hC0 : S1.foldl CapModel.capBF [] = S1.foldl CapModel.capFF [] := by
    rw [← CapModel.run_bf_caps, ← CapModel.run_ff_caps, hK1]
  have hI1 : IsList S1 := fun x hx => hL x (hS1mem x hx)
  have hC : ∀ i j, i < j → j < (S1.foldl CapModel.capFF []).length →
      1 / 3 ≤ (S1.foldl CapModel.capFF []).getD i 0 →
      1 / 3 ≤ (S1.foldl CapModel.capFF []).getD j 0 →
      (S1.foldl CapModel.capFF []).getD i 0 ≤ (S1.foldl CapModel.capFF []).getD j 0 := by
    intro i j hij hj hi' hj'
    rw [← CapModel.run_ff_caps] at hj hi' hj' ⊢
    have hjl : j < (run ffChoice S1).length := by simpa using hj
    have hil : i < (run ffChoice S1).length := by omega
    rw [List.getD_eq_getElem _ _ (by simpa using hil), List.getElem_map] at hi' ⊢
    rw [List.getD_eq_getElem _ _ (by simpa using hjl), List.getElem_map] at hj' ⊢
    have hA := ff_bigs_levels_antitone S1 hS1pw hI1 S1.length i j hij
      (by rw [List.take_length]; exact hjl)
      (by rw [List.take_length, List.getD_eq_getElem _ _ hjl]; linarith)
    rw [List.take_length, List.getD_eq_getElem _ _ hjl, List.getD_eq_getElem _ _ hil] at hA
    linarith
  have hT : ∀ x ∈ S2, 1 / 6 ≤ x ∧ x ≤ 1 / 3 := fun x hx => ⟨h6 x (hS2mem x hx), hS2le x hx⟩
  have key := Phase2.phase2 (S1.foldl CapModel.capFF []) hC S2 hT hS2pw
  unfold BFD FFD
  rw [CapModel.BF_eq_caps, CapModel.FF_eq_caps, hsplit, List.foldl_append, List.foldl_append, hC0]
  exact key

end BinPacking.Decreasing.Glue

open BinPacking.Decreasing in
theorem solution (L : List ℝ) (hL : IsList L) (h6 : ∀ a ∈ L, (1 / 6 : ℝ) ≤ a) :
    BFD L ≤ FFD L := by
  exact BinPacking.Decreasing.Glue.bfd_le_ffd_main L hL h6
