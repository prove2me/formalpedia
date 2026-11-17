-- Prove2me | solution 1 for FLT.EDS.mk_C_injective
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:42.205332+00:00
-- url     : https://prove2.me/submissions/18ee08ab-752c-439a-a7bf-3e212595a0cd

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_WardSomos

/-! Proofs of the lemmas stated in `Theorems.Thm_EDS_PreDivisionAdjacentRelations` and their helpers. -/
open Polynomial WeierstrassCurve

open scoped Classical

namespace FLT.EDS

variable {R : Type*} [CommRing R]

/-- Descent: `mk ∘ C : R[X] → CoordinateRing` is injective (the rank-1 component of the free
rank-2 basis `{1, mk Y}`).  Lets us check any `R[X]` polynomial identity in the coordinate ring. -/
theorem _root_.solution (W : WeierstrassCurve R) :
    Function.Injective (fun p : R[X] => Affine.CoordinateRing.mk W (Polynomial.C p)) := by
  intro p q hpq
  simp only at hpq
  have hsub : Affine.CoordinateRing.mk W (Polynomial.C (p - q)) = 0 := by
    have h : Affine.CoordinateRing.mk W (Polynomial.C (p - q))
        = Affine.CoordinateRing.mk W (Polynomial.C p) - Affine.CoordinateRing.mk W (Polynomial.C q) := by
      rw [map_sub, map_sub]
    rw [h, hpq, sub_self]
  have hsmul : (p - q) • (1 : Affine.CoordinateRing W)
      + (0 : R[X]) • Affine.CoordinateRing.mk W Polynomial.X = 0 := by
    rw [zero_smul, add_zero, Affine.CoordinateRing.smul, mul_one]; exact hsub
  exact sub_eq_zero.mp (Affine.CoordinateRing.smul_basis_eq_zero hsmul).1

end FLT.EDS
