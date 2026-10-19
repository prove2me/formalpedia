-- Prove2me | solution 1 for CompactnessConjecture.coordinateCenterLine_direction_det_ne_zero_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/d5a9de20-d259-4405-9ca1-6a74ed657753

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {x y x' y' : K}
    (hxy : x ≠ 0 ∨ y ≠ 0)
    (hxy' : x' ≠ 0 ∨ y' ≠ 0)
    (hne : coordinateCenterLine K x y hxy ≠
      coordinateCenterLine K x' y' hxy') :
    x * y' - x' * y ≠ 0 := by
  intro hdet
  have hscale :
      ∃ t : K, t ≠ 0 ∧ x' = t * x ∧ y' = t * y := by
    rcases hxy with hx | hy
    · let t : K := x' / x
      have hfirst : x' = t * x := by
        dsimp [t]
        field_simp [hx]
      have hsecond : y' = t * y := by
        dsimp [t]
        field_simp [hx]
        linear_combination hdet
      have ht : t ≠ 0 := by
        intro htzero
        have hxzero := hfirst
        have hyzero := hsecond
        rw [htzero, zero_mul] at hxzero hyzero
        exact hxy'.elim (fun h => h hxzero)
          (fun h => h hyzero)
      exact ⟨t, ht, hfirst, hsecond⟩
    · let t : K := y' / y
      have hsecond : y' = t * y := by
        dsimp [t]
        field_simp [hy]
      have hfirst : x' = t * x := by
        dsimp [t]
        field_simp [hy]
        linear_combination -hdet
      have ht : t ≠ 0 := by
        intro htzero
        have hxzero := hfirst
        have hyzero := hsecond
        rw [htzero, zero_mul] at hxzero hyzero
        exact hxy'.elim (fun h => h hxzero)
          (fun h => h hyzero)
      exact ⟨t, ht, hfirst, hsecond⟩
  obtain ⟨t, ht, hfirst, hsecond⟩ := hscale
  apply hne
  apply Subtype.ext
  change
    LinearMap.range (coordinateCenterLinearMap K x y) =
      LinearMap.range (coordinateCenterLinearMap K x' y')
  have hmap (u : Fin 2 → K) :
      coordinateCenterLinearMap K x' y' u =
        t • coordinateCenterLinearMap K x y u := by
    funext i
    fin_cases i <;>
      simp [coordinateCenterLinearMap,
        symplecticHorizontalVector,
        symplecticAnnihilatorVector,
        smul_eq_mul, hfirst, hsecond] <;>
      ring
  apply le_antisymm
  · intro w hw
    obtain ⟨u, rfl⟩ := hw
    refine ⟨t⁻¹ • u, ?_⟩
    rw [hmap, map_smul]
    simp [ht]
  · intro w hw
    obtain ⟨u, rfl⟩ := hw
    refine ⟨t • u, ?_⟩
    rw [map_smul, ← hmap]
end CompactnessConjecture
