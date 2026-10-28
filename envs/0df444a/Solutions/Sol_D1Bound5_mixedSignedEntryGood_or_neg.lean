-- Prove2me | solution 1 for D1Bound5.mixedSignedEntryGood_or_neg
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:51:59.67912+00:00
-- url     : https://prove2.me/submissions/bb68062a-4047-40a1-8336-0d1d76a4c2e5

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
import Theorems.Thm_D1Bound5_signedEntryBounds_nine_or_neg
import Theorems.Thm_D1Bound5_signedEntryBounds_three_or_neg

section
namespace D1Bound5















theorem _root_.solution {R : Type*} [CommRing R]
    (f : R →+* ℂ) (a : Fin 4 → R) (u : Fin 4 → ℂ)
    (i j : Fin 4) (r : R)
    (hu : ∀ k, (u k)^2 = f (a k))
    (hr : r^2 = a i*a j+1)
    (hfirst : i = 0 ∨ j = 0 → 3 ≤ ‖f (a i) * f (a j)‖)
    (hlater : ¬(i = 0 ∨ j = 0) → 9 ≤ ‖f (a i) * f (a j)‖) :
    MixedSignedEntryGood f a u i j r ∨
      MixedSignedEntryGood f a u i j (-r) := by
  unfold MixedSignedEntryGood
  split_ifs with h
  · exact signedEntryBounds_three_or_neg f (a i) (a j) r (u i) (u j)
      (hu i) (hu j) hr (hfirst h)
  · exact signedEntryBounds_nine_or_neg f (a i) (a j) r (u i) (u j)
      (hu i) (hu j) hr (hlater h)

end D1Bound5
namespace D1Bound5





end D1Bound5
end
