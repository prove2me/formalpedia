-- Prove2me | solution 1 for DeletionHash.MixedEdit.confusable_record
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:35:55.070504+00:00
-- url     : https://prove2.me/submissions/4805fd6c-7225-4fb0-a40f-1cecf4847524

import Definitions.Def_DeletionHash_MixedEdit_Channel

open DeletionHash.MixedEdit
universe u

private theorem replace_parts {α : Type*} (b : ℕ) (a u v c : List α)
    (hu : u.length ≤ b) (hv : v.length ≤ b) (hne : u ≠ v) :
    let e : Edit α := ⟨a.length, u.length, v⟩
    ValidEdit b (a ++ u ++ c) e ∧ applyEdit e (a ++ u ++ c) = a ++ v ++ c := by
  dsimp
  constructor
  · simp only [ValidEdit, window, List.length_append]
    refine ⟨by omega, hu, hv, ?_⟩
    simpa [List.append_assoc] using hne
  · simp [applyEdit, List.append_assoc, ← List.drop_drop]

private theorem reverse_edit {α : Type*} {b : ℕ} {x : List α} {e : Edit α}
    (he : ValidEdit b x e) :
    ∃ f : Edit α, ValidEdit b (applyEdit e x) f ∧ applyEdit f (applyEdit e x) = x := by
  let a := x.take e.position
  let u := window e.removed x e.position
  let c := x.drop (e.position + e.removed)
  have hp : e.position ≤ x.length := by have := he.1; omega
  have ha : a.length = e.position := by simp [a, List.length_take, Nat.min_eq_left hp]
  have hu : u.length = e.removed := by
    simp only [u, window, List.length_take, List.length_drop]
    exact Nat.min_eq_left (by have := he.1; omega)
  have hx : a ++ u ++ c = x := by
    dsimp [a, u, c, window]
    rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have hy : applyEdit e x = a ++ e.replacement ++ c := rfl
  let f : Edit α := ⟨a.length, e.replacement.length, u⟩
  obtain ⟨hf, hback⟩ := replace_parts b a e.replacement u c he.2.2.1
    (by rw [hu]; exact he.2.1) (Ne.symm he.2.2.2)
  exact ⟨f, by simpa only [hy] using hf, by simpa only [hy, hx] using hback⟩

private theorem append_valid {α : Type*} {b : ℕ} {x : List α}
    {r s : List (Edit α)} (hr : ValidRecord b x r)
    (hs : ValidRecord b (target x r) s) : ValidRecord b x (r ++ s) := by
  induction r generalizing x with
  | nil => simpa [target] using hs
  | cons e r ih =>
    exact ⟨hr.1, ih hr.2 hs⟩

private theorem reverse_record {α : Type*} {b : ℕ} {x : List α}
    {r : List (Edit α)} (hr : ValidRecord b x r) :
    ∃ s : List (Edit α), s.length = r.length ∧
      ValidRecord b (target x r) s ∧ target (target x r) s = x := by
  induction r generalizing x with
  | nil => exact ⟨[], rfl, trivial, rfl⟩
  | cons e r ih =>
    obtain ⟨s, hlen, hs, htarget⟩ := ih hr.2
    obtain ⟨f, hf, hback⟩ := reverse_edit hr.1
    refine ⟨s ++ [f], by simp [hlen], append_valid hs ?_, ?_⟩
    · change ValidRecord b (target (target (applyEdit e x) r) s) [f]
      rw [htarget]
      exact ⟨hf, trivial⟩
    · change target (target (applyEdit e x) r) (s ++ [f]) = x
      simp only [target, List.foldl_append, List.foldl_cons, List.foldl_nil] at htarget ⊢
      rw [htarget]
      exact hback

theorem solution {α : Type u} [Fintype α] [DecidableEq α]
    (t b : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) (hq : 2 ≤ Fintype.card α)
    (x z : List α) (hne : x ≠ z) (hconf : Confusable b t x z) :
    ∃ record : List (Edit α), record.length ≤ 2*t ∧ ValidRecord b x record ∧ target x record = z := by
  obtain ⟨y, ⟨r, hrlen, hr, hry⟩, ⟨s, hslen, hs, hsy⟩⟩ := hconf
  obtain ⟨s', hs'len, hs', hs'target⟩ := reverse_record hs
  have hsame : target x r = target z s := hry.trans hsy.symm
  refine ⟨r ++ s', ?_, append_valid hr (hsame.symm ▸ hs'), ?_⟩
  · simp only [List.length_append, hs'len]
    omega
  · have happ : target x (r ++ s') = target (target x r) s' := List.foldl_append
    rw [happ]
    rw [hsame]
    exact hs'target

#print axioms solution
