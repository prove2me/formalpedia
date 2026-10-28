-- Prove2me | solution 1 for D1Bound5.normalizedRootError_diag
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:18:22.404205+00:00
-- url     : https://prove2.me/submissions/7ce3077e-2b62-4f05-8028-26228d176d8c

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions

section
open scoped BigOperators
open Matrix

namespace D1Bound5











/-- The correction is zero on the diagonal. -/
theorem _root_.solution {R n : Type*} [CommRing R]
    (a u : n → R) (M : Matrix n n R)
    (hu : ∀ i, (u i)^2 = a i) (hd : ∀ i, M i i = a i)
    (i : n) : normalizedRootError a u M i i = 0 := by
  simp only [normalizedRootError, scaledRootMatrix, hd i]
  have h := hu i
  calc
    u i * a i * u i - a i * a i =
        (u i)^2 * a i - a i^2 := by ring
    _ = 0 := by rw [h]; ring







end D1Bound5
end
