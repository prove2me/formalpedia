-- Prove2me | solution 1 for FongoSync.fold_keep_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:00:33.739033+00:00
-- url     : https://prove2.me/submissions/7a2f73f4-9b8a-460b-8199-4977e104371e

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
import Theorems.Thm_FongoSync_keep_some
import Theorems.Thm_FongoSync_isLE_of_not_lt

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {E K : Type} (cmp : K → K → Ordering) (key : E → K)
variable [TransCmp cmp] [LawfulEqCmp cmp]
variable {cmp key}
namespace FongoSync
theorem _root_.solution (l : List E) (h : Option E) (m : E)
    (hm : l.foldl (keep cmp key) h = some m) :
    (h = some m ∨ m ∈ l) ∧ (∀ x ∈ l, (cmp (key x) (key m)).isLE) ∧
      (∀ s, h = some s → (cmp (key s) (key m)).isLE) := by
  induction l generalizing h with
  | nil =>
    simp only [List.foldl] at hm
    subst hm
    exact ⟨.inl rfl, by simp, fun s hs => by cases hs; exact ReflCmp.isLE_rfl⟩
  | cons x xs ih =>
    simp only [List.foldl] at hm
    have ⟨hmem, hall, hheld⟩ := ih _ hm
    -- what `keep h x` holds is at least `x` and at least what `h` held
    have hx : ∀ s, keep cmp key h x = some s →
        (cmp (key x) (key s)).isLE ∧ (∀ t, h = some t → (cmp (key t) (key s)).isLE) ∧
        (s = x ∨ h = some s) := by
      intro s hs
      cases h with
      | none =>
        simp only [keep, Option.some.injEq] at hs; subst hs
        exact ⟨ReflCmp.isLE_rfl, by simp, .inl rfl⟩
      | some t =>
        rw [keep_held] at hs
        by_cases hlt : cmp (key t) (key x) = .lt
        · simp only [hlt, ↓reduceIte, Option.some.injEq] at hs; subst hs
          exact ⟨ReflCmp.isLE_rfl, fun t' ht' => by cases ht'; rw [hlt]; rfl, .inl rfl⟩
        · simp only [hlt, ↓reduceIte, Option.some.injEq] at hs; subst hs
          exact ⟨isLE_of_not_lt hlt, fun t' ht' => by cases ht'; exact ReflCmp.isLE_rfl, .inr rfl⟩
    have ⟨s, hs⟩ := keep_some (cmp := cmp) (key := key) h x
    have ⟨hxs, hts, hsx⟩ := hx s hs
    have hsm := hheld s hs
    refine ⟨?_, ?_, ?_⟩
    · rcases hmem with hmem | hmem
      · rw [hs] at hmem
        cases hmem
        rcases hsx with rfl | rfl
        · exact .inr (.head _)
        · exact .inl rfl
      · exact .inr (.tail _ hmem)
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact TransCmp.isLE_trans hxs hsm
      · exact hall y hy
    · intro t ht
      exact TransCmp.isLE_trans (hts t ht) hsm
end FongoSync
