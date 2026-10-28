-- Prove2me | solution 1 for D1Bound5.signed_entry_good_or_neg
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:20:16.803032+00:00
-- url     : https://prove2.me/submissions/7bfe3ff0-3fd7-46db-86dc-1f242ca4081b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_RootMatrixSigns_Definitions
import Theorems.Thm_D1Bound5_exists_small_normalized_root_error

section
namespace D1Bound5



/-- One of the two integral signs satisfies both normalized bounds.
The proof uses only the two possible signs of an existing root. -/
theorem _root_.solution {R : Type*} [CommRing R]
    (f : R →+* ℂ) (a b r : R) (u v : ℂ)
    (hu : u^2 = f a) (hv : v^2 = f b)
    (hr : r^2 = a*b+1) (hab : 9 ≤ ‖f a * f b‖) :
    SignedEntryGood f a b u v r ∨ SignedEntryGood f a b u v (-r) := by
  have hrC : (f r)^2 = f a * f b + 1 := by
    have h := congrArg f hr
    simpa only [map_pow, map_mul, map_add, map_one] using h
  obtain ⟨t, ht, hnear, hhalf⟩ :=
    exists_small_normalized_root_error (f a) (f b) u v (f r) hu hv hrC hab
  rcases ht with h | h
  · left
    simpa only [SignedEntryGood, ← h] using And.intro hnear hhalf
  · right
    have hsign : u * f (-r) * v = t := by
      rw [h, map_neg]
      ring
    simpa only [SignedEntryGood, hsign] using And.intro hnear hhalf

end D1Bound5

namespace D1Bound5





end D1Bound5

namespace D1Bound5



end D1Bound5
end
