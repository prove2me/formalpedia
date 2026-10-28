-- Prove2me | solution 1 for D1Bound5.signedEntryBounds_three_or_neg
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:22:19.226455+00:00
-- url     : https://prove2.me/submissions/70241fce-25c2-408b-abee-9a9ea986e285

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
import Theorems.Thm_D1Bound5_exists_root_error_three

section
namespace D1Bound5





theorem _root_.solution {R : Type*} [CommRing R]
    (f : R →+* ℂ) (a b r : R) (u v : ℂ)
    (hu : u^2 = f a) (hv : v^2 = f b)
    (hr : r^2 = a*b+1) (hab : 3 ≤ ‖f a * f b‖) :
    SignedEntryBounds f a b u v r (5/9) (25/486) ∨
      SignedEntryBounds f a b u v (-r) (5/9) (25/486) := by
  have ht : (u * f r * v)^2 = (f a * f b) * (f a * f b + 1) := by
    rw [mul_pow, mul_pow, hu, hv]
    have h := congrArg f hr
    simp only [map_pow, map_mul, map_add, map_one] at h
    rw [h]
    ring
  obtain ⟨t, ht', hn, he⟩ :=
    exists_root_error_three (f a * f b) (u * f r * v) hab ht
  rcases ht' with ht' | ht'
  · left
    simpa only [SignedEntryBounds, ← ht'] using And.intro hn he
  · right
    have hsign : u * f (-r) * v = t := by
      rw [ht', map_neg]
      ring
    simpa only [SignedEntryBounds, hsign] using And.intro hn he











end D1Bound5
namespace D1Bound5





end D1Bound5
end
