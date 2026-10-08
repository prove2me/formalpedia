-- Prove2me | solution 1 for BinPacking.Decreasing.bfd_follows_ffd_large_items
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T05:02:37.028857+00:00
-- url     : https://prove2.me/submissions/9b2e9b10-78c0-4448-803b-ba8e9d95e1b3

import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model

set_option autoImplicit false

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

open BinPacking.Decreasing in
theorem solution (L : List ℝ) (hL : IsList L)
    (h6 : ∀ a ∈ L, (1 / 6 : ℝ) ≤ a) (i : Fin (sortDesc L).length)
    (hi : (i : ℕ) < ((sortDesc L).filter (fun a => decide ((1 / 3 : ℝ) < a))).length) :
    binOf bfChoice (sortDesc L) i = binOf ffChoice (sortDesc L) i ∧
      slotOf bfChoice (sortDesc L) i = slotOf ffChoice (sortDesc L) i := by
  apply BfdFfdLarge.core _ _ i hi
  have := List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
    (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; linarith)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _) L
  simp only [decide_eq_true_eq] at this
  exact this
