-- Prove2me | solution 1 for CubicSurface27.blowup_intersection_form
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T20:35:00.02917+00:00
-- url     : https://prove2.me/submissions/605cc0c0-1090-4ac2-9638-46f9c858f215

import Mathlib
import Definitions.Def_blowup_lattice_27
open Finset

open CubicSurface27 in
theorem solution :
    inter classL classL = 1 ∧
    (∀ i : Fin 6, inter classL (classE i) = 0) ∧
    (∀ i j : Fin 6, i ≠ j → inter (classE i) (classE j) = 0) ∧
    (∀ i : Fin 6, inter (classE i) (classE i) = -1) ∧
    inter classH classH = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [inter, classL]
  · intro i
    simp [inter, classL, classE]
  · intro i j hij
    have h : ∀ k : Fin 6, (if k = i then (-1 : ℤ) else 0) * (if k = j then (-1 : ℤ) else 0) = 0 := by
      intro k
      by_cases h1 : k = i
      · have h2 : k ≠ j := fun h => hij (h1 ▸ h)
        simp [h2]
      · simp [h1]
    simp [inter, classE, h]
  · intro i
    have h : ∀ k : Fin 6, (if k = i then (-1 : ℤ) else 0) * (if k = i then (-1 : ℤ) else 0)
        = if k = i then 1 else 0 := by
      intro k
      by_cases h1 : k = i <;> simp [h1]
    simp [inter, classE, h]
  · simp [inter, classH]
