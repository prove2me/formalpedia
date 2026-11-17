-- Prove2me | solution 1 for FLT.EDS.mk_psi_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:42.748164+00:00
-- url     : https://prove2.me/submissions/8ea0ea3b-0e78-44d6-9f53-2368756aada2

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

/-- ψ ↔ preΨ in the coordinate ring: `mk(ψ n) = mk(C preΨ n) · (ψ₂ if n even else 1)`.
From `mk_ψ` and the definition `Ψ n = C(preΨ n)·(ψ₂ if even else 1)`. -/
theorem _root_.solution (W : WeierstrassCurve R) (n : ℤ) :
    Affine.CoordinateRing.mk W (W.ψ n)
      = Affine.CoordinateRing.mk W (Polynomial.C (W.preΨ n))
          * (if Even n then Affine.CoordinateRing.mk W W.ψ₂ else 1) := by
  rw [Affine.CoordinateRing.mk_ψ, WeierstrassCurve.Ψ, map_mul, apply_ite (Affine.CoordinateRing.mk W),
    map_one]

end FLT.EDS
