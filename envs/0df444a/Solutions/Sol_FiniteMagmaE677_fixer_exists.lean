-- Prove2me | solution 1 for FiniteMagmaE677.fixer_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-11T03:02:51.769054+00:00
-- url     : https://prove2.me/submissions/4846445a-a223-47a5-8bbc-e720b77f4391
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_FiniteMagmaE677_orbit_right_collision_or_fixer
import Theorems.Thm_FiniteMagmaE677_two_left_orbit_complement_elements_escape_gives_fixer
import Theorems.Thm_FiniteMagmaE677_unique_left_orbit_complement_escape_gives_fixer
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Conditional fixer-existence decomposition

This module reduces fixer existence to the orbit-collision theorem and the two cases for
the complement of the left orbit. The imported child statements remain open problems.
-/

universe u

theorem solution {α : Type u} [Fintype α] (op : α → α → α)
    (h : FiniteMagmaE677.E677 op) (x : α) : ∃ y : α, op y x = x := by
  classical
  by_contra hnofix
  have hcollision := FiniteMagmaE677.orbit_right_collision_or_fixer op h x
  have horbit_inj : ∀ {a b : α},
      FiniteMagmaE677.InLeftOrbit op x a →
        FiniteMagmaE677.InLeftOrbit op x b →
          op a x = op b x → a = b := by
    intro a b ha hb hab
    rcases hcollision ha hb hab with hab | hfix
    · exact hab
    · exact (hnofix hfix).elim
  have hni : op x x ≠ x := by
    intro hxx
    exact hnofix ⟨x, hxx⟩
  by_cases hfull : ∀ a : α, FiniteMagmaE677.InLeftOrbit op x a
  · have hinjective : Function.Injective (fun a : α => op a x) := by
      intro a b hab
      exact horbit_inj (hfull a) (hfull b) hab
    have hsurjective : Function.Surjective (fun a : α => op a x) :=
      Finite.injective_iff_surjective.mp hinjective
    exact hnofix (hsurjective x)
  · push Not at hfull
    obtain ⟨A, hA_notin⟩ := hfull
    by_cases hescape : ∃ a : α,
        FiniteMagmaE677.InLeftOrbit op x a ∧
          ¬ FiniteMagmaE677.InLeftOrbit op x (op a x)
    · by_cases htwo : ∃ a b : α,
          a ≠ b ∧
            ¬ FiniteMagmaE677.InLeftOrbit op x a ∧
              ¬ FiniteMagmaE677.InLeftOrbit op x b
      · exact hnofix
          (FiniteMagmaE677.two_left_orbit_complement_elements_escape_gives_fixer
            op h x hni htwo hescape)
      · have hA_unique : ∀ a : α,
            ¬ FiniteMagmaE677.InLeftOrbit op x a → a = A := by
          intro a ha
          by_contra haA
          exact htwo ⟨a, A, haA, ha, hA_notin⟩
        exact hnofix
          (FiniteMagmaE677.unique_left_orbit_complement_escape_gives_fixer
            op h x A hni hA_notin hA_unique hescape)
    · push Not at hescape
      let S : Finset α :=
        Finset.univ.filter (FiniteMagmaE677.InLeftOrbit op x)
      have hmem : ∀ a : α,
          a ∈ S ↔ FiniteMagmaE677.InLeftOrbit op x a := by
        intro a
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      have hxS : x ∈ S := (hmem x).mpr ⟨0, rfl⟩
      have hMapsTo : Set.MapsTo (fun a : α => op a x) (S : Set α) (S : Set α) := by
        intro a ha
        exact (hmem _).mpr (hescape a ((hmem a).mp ha))
      have hInjOn : Set.InjOn (fun a : α => op a x) (S : Set α) := by
        intro a ha b hb hab
        exact horbit_inj ((hmem a).mp ha) ((hmem b).mp hb) hab
      have hSurjOn : Set.SurjOn (fun a : α => op a x) (S : Set α) (S : Set α) :=
        Finset.surjOn_of_injOn_of_card_le _ hMapsTo hInjOn (le_refl _)
      obtain ⟨y, _hyS, hy⟩ := hSurjOn hxS
      exact hnofix ⟨y, hy⟩
