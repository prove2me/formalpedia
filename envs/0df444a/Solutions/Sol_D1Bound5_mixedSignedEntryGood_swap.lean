-- Prove2me | solution 1 for D1Bound5.mixedSignedEntryGood_swap
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:51:56.425918+00:00
-- url     : https://prove2.me/submissions/f6c9ec49-b1a6-4e96-ac62-178b6ae9d781

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_MixedRootMatrixSigns_Definitions
import Theorems.Thm_D1Bound5_signedEntryBounds_swap

section
namespace D1Bound5













theorem _root_.solution {R : Type*} [CommRing R]
    (f : R →+* ℂ) (a : Fin 4 → R) (u : Fin 4 → ℂ)
    (i j : Fin 4) (r : R)
    (h : MixedSignedEntryGood f a u i j r) :
    MixedSignedEntryGood f a u j i r := by
  by_cases hi : i = 0 ∨ j = 0
  · have hj : j = 0 ∨ i = 0 := by tauto
    have hx : SignedEntryBounds f (a i) (a j) (u i) (u j) r (5/9) (25/486) := by
      simpa [MixedSignedEntryGood, hi] using h
    simpa [MixedSignedEntryGood, hj] using
      signedEntryBounds_swap f (a i) (a j) r (u i) (u j) (5/9) (25/486) hx
  · have hj : ¬(j = 0 ∨ i = 0) := by tauto
    have hx : SignedEntryBounds f (a i) (a j) (u i) (u j) r (7/13) (1/64) := by
      simpa [MixedSignedEntryGood, hi] using h
    simpa [MixedSignedEntryGood, hj] using
      signedEntryBounds_swap f (a i) (a j) r (u i) (u j) (7/13) (1/64) hx



end D1Bound5
namespace D1Bound5





end D1Bound5
end
