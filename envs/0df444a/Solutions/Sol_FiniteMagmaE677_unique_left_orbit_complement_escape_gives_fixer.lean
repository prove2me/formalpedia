-- Prove2me | solution 1 for FiniteMagmaE677.unique_left_orbit_complement_escape_gives_fixer
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-11T03:26:17.689241+00:00
-- url     : https://prove2.me/submissions/015d589f-cf1f-4166-8094-01fc66b6c9ae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Finset.Card
import Theorems.Thm_FiniteMagmaE677_orbit_right_collision_or_fixer
import Theorems.Thm_FiniteMagmaE677_unique_left_orbit_complement_collision_gives_fixer

/-!
# Reduction of the one-element orbit-complement case

This module reduces the one-element complement escape theorem to the orbit-collision
theorem and a collision between the orbit and its unique complement element.
-/

universe u

theorem solution
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x A : α) (hni : op x x ≠ x)
    (hA_notin : ¬ FiniteMagmaE677.InLeftOrbit op x A)
    (hA_unique : ∀ a : α, ¬ FiniteMagmaE677.InLeftOrbit op x a → a = A)
    (_hescape : ∃ a : α,
      FiniteMagmaE677.InLeftOrbit op x a ∧
        ¬ FiniteMagmaE677.InLeftOrbit op x (op a x)) :
    FiniteMagmaE677.HasFixerAt op x := by
  classical
  by_contra hnofix
  have horbit_collision := FiniteMagmaE677.orbit_right_collision_or_fixer op h x
  have horbit_inj : ∀ {a b : α},
      FiniteMagmaE677.InLeftOrbit op x a →
        FiniteMagmaE677.InLeftOrbit op x b →
          op a x = op b x → a = b := by
    intro a b ha hb hab
    rcases horbit_collision ha hb hab with hab | hfix
    · exact hab
    · exact (hnofix hfix).elim
  have horbit_iff_neA (a : α) :
      FiniteMagmaE677.InLeftOrbit op x a ↔ a ≠ A := by
    constructor
    · intro ha haA
      exact hA_notin (haA ▸ ha)
    · intro haA
      by_contra ha
      exact haA (hA_unique a ha)
  let S : Finset α := Finset.univ.filter (FiniteMagmaE677.InLeftOrbit op x)
  let T : Finset α := Finset.univ.erase x
  have hmemS (a : α) : a ∈ S ↔ FiniteMagmaE677.InLeftOrbit op x a := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hST_card : T.card ≤ S.card := by
    have hS : S = Finset.univ.erase A := by
      ext a
      simp only [hmemS, Finset.mem_erase, Finset.mem_univ, and_true, horbit_iff_neA]
    rw [hS]
    simp only [T, Finset.card_erase_of_mem, Finset.mem_univ]
    exact le_rfl
  have hMapsTo : Set.MapsTo (fun a : α ↦ op a x) (S : Set α) (T : Set α) := by
    intro a ha
    simp only [T, Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
      Set.mem_singleton_iff, true_and]
    intro hax
    exact hnofix ⟨a, hax⟩
  have hInjOn : Set.InjOn (fun a : α ↦ op a x) (S : Set α) := by
    intro a ha b hb hab
    exact horbit_inj ((hmemS a).mp ha) ((hmemS b).mp hb) hab
  have hSurjOn : Set.SurjOn (fun a : α ↦ op a x) (S : Set α) (T : Set α) :=
    Finset.surjOn_of_injOn_of_card_le _ hMapsTo hInjOn hST_card
  have hAxT : op A x ∈ T := by
    simp only [T, Finset.mem_erase, Finset.mem_univ, and_true]
    intro hAx
    exact hnofix ⟨A, hAx⟩
  obtain ⟨a, haS, haA⟩ := hSurjOn hAxT
  exact hnofix
    (FiniteMagmaE677.unique_left_orbit_complement_collision_gives_fixer
      op h x A hni hA_notin hA_unique ⟨a, (hmemS a).mp haS, haA⟩)
