-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.saturated_coordinate_covering
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/69fa1a0b-bc50-4798-bb18-ceb369edc876

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution {H m s : ℕ}
    (A : Fin s → (Fin m → Fin H) → Fin H)
    (hA : IsSaturated A) (hH : 0 < H) (hms : m ≤ s) :
    ∃ f g : (Fin s → Fin H) → (Fin s → Fin H),
      ∀ x y : Fin s → Fin H,
        (∃ row : Fin s, x row = f y row) ∨
        (∃ row : Fin s, y row = g x row) := by
  classical
  refine ⟨forwardGuess A hA hH hms, backwardGuess A hms, ?_⟩
  intro x y
  by_cases hback : ∃ row : Fin s, y row = backwardGuess A hms x row
  · exact Or.inr hback
  · left
    let z : Fin m → Fin H := fun coordinate => x (Fin.castLE hms coordinate)
    have hz : z ∈ exceptionalColumns A y := by
      apply (mem_exceptionalColumns A y z).mpr
      intro row heq
      apply hback
      refine ⟨row, ?_⟩
      simpa [backwardGuess, z] using heq.symm
    let ez : exceptionalColumns A y := ⟨z, hz⟩
    let index := exceptionalColumnIndex A hA y
    let row : Fin s := Fin.castLE hms (index ez)
    refine ⟨row, ?_⟩
    have hexists : ∃ w : exceptionalColumns A y,
        Fin.castLE hms (index w) = row := ⟨ez, rfl⟩
    have hindex : index (Classical.choose hexists) = index ez :=
      Fin.castLE_injective hms (Classical.choose_spec hexists)
    have hchosen : Classical.choose hexists = ez := index.injective hindex
    change x row =
      if h : ∃ w : exceptionalColumns A y,
          Fin.castLE hms (index w) = row then
        (Classical.choose h).val (index (Classical.choose h))
      else
        ⟨0, hH⟩
    rw [dif_pos hexists, hchosen]
end ErdosProblems.MulticolourTriangleRamsey
