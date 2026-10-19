-- Prove2me | solution 1 for CompactnessConjecture.symplecticCanonical_line_no_three_common_centers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/bd6c3ed5-7466-4c2b-80d9-017f4a3f624f

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symmetricGraphLine_odd_no_three_actual_centers
import Theorems.Thm_CompactnessConjecture_symplecticLine_eq_invertible_symmetricGraphLine
import Theorems.Thm_CompactnessConjecture_symplecticLine_eq_coordinateCenterLine_of_common_points
import Theorems.Thm_CompactnessConjecture_coordinateCenterLine_direction_det_ne_zero_of_ne

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (htwo : (2 : K) ≠ 0)
    (X : SymplecticLine K)
    (hXH :
      Disjoint X.1 (symmetricGraphLine K 0 0 0).1)
    (hXV :
      Disjoint X.1 (symplecticVerticalLine K).1)
    (centers : Fin 3 → SymplecticLine K)
    (hcenters : Function.Injective centers)
    (hH : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K 0 0 0).1 ∧
          p.1 ≤ (centers i).1)
    (hV : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symplecticVerticalLine K).1 ∧
          p.1 ≤ (centers i).1)
    (hX : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X.1 ∧ p.1 ≤ (centers i).1) :
    False := by
  classical
  obtain ⟨a, b, c, hXgraph, hdet⟩ :=
    symplecticLine_eq_invertible_symmetricGraphLine
      K X hXV hXH
  choose pH hpHH hpHC using hH
  choose pV hpVV hpVC using hV
  have hclass (i : Fin 3) :
      ∃ (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0),
        centers i = coordinateCenterLine K x y hxy :=
    symplecticLine_eq_coordinateCenterLine_of_common_points
      K (centers i) (pH i) (pV i)
      (hpHH i) (hpHC i) (hpVV i) (hpVC i)
  choose x y hxy hrepr using hclass
  have hdir {i j : Fin 3} (hij : i ≠ j) :
      x i * y j - x j * y i ≠ 0 := by
    apply coordinateCenterLine_direction_det_ne_zero_of_ne
      K (hxy i) (hxy j)
    intro heq
    apply hij
    apply hcenters
    exact (hrepr i).trans (heq.trans (hrepr j).symm)
  have h01 : x 0 * y 1 - x 1 * y 0 ≠ 0 :=
    hdir (by decide : (0 : Fin 3) ≠ 1)
  have h02 : x 0 * y 2 - x 2 * y 0 ≠ 0 :=
    hdir (by decide : (0 : Fin 3) ≠ 2)
  have h12 : x 1 * y 2 - x 2 * y 1 ≠ 0 :=
    hdir (by decide : (1 : Fin 3) ≠ 2)
  apply symmetricGraphLine_odd_no_three_actual_centers K
    htwo hdet h01 h02 h12
  · obtain ⟨p, hpX, hpC⟩ := hX 0
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 0]
      exact hpC
  · obtain ⟨p, hpX, hpC⟩ := hX 1
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 1]
      exact hpC
  · obtain ⟨p, hpX, hpC⟩ := hX 2
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 2]
      exact hpC
end CompactnessConjecture
