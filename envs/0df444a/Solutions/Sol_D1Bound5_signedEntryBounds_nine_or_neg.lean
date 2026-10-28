-- Prove2me | solution 1 for D1Bound5.signedEntryBounds_nine_or_neg
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:49:48.694708+00:00
-- url     : https://prove2.me/submissions/43fb5676-74c8-4fad-ae20-a67600e916a7

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
import Definitions.Def_D1Bound5_RootMatrixSigns_Definitions
import Theorems.Thm_D1Bound5_signed_entry_good_or_neg

section
namespace D1Bound5









/-- The nine-threshold estimate is already stronger than the requested
twelve-threshold constants: 16/31 < 7/13 and 128/8649 < 1/64.
This avoids any unproved B*C >= 12 assumption for ordered quadruples. -/
theorem _root_.solution {R : Type*} [CommRing R]
    (f : R →+* ℂ) (a b r : R) (u v : ℂ)
    (hu : u^2 = f a) (hv : v^2 = f b)
    (hr : r^2 = a*b+1) (hab : 9 ≤ ‖f a * f b‖) :
    SignedEntryBounds f a b u v r (7/13) (1/64) ∨
      SignedEntryBounds f a b u v (-r) (7/13) (1/64) := by
  have h1 : (16/31 : ℝ) < 7/13 := by norm_num
  have h2 : (128/8649 : ℝ) < 1/64 := by norm_num
  rcases signed_entry_good_or_neg f a b r u v hu hv hr hab with h | h
  · exact Or.inl ⟨lt_trans h.1 h1, lt_trans h.2 h2⟩
  · exact Or.inr ⟨lt_trans h.1 h1, lt_trans h.2 h2⟩







end D1Bound5
namespace D1Bound5





end D1Bound5
end
