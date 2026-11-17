-- Prove2me | solution 1 for FLT.EDS.prePsi_adjacent_somos
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:45.241781+00:00
-- url     : https://prove2.me/submissions/a85152cf-3274-4e3d-9e61-86046866b5b3

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Theorems.Thm_FLT_EDS_normEDS_adjacent_somos
import Definitions.Def_WardSomos
import Theorems.Thm_FLT_EDS_mk_psi_eq
import Theorems.Thm_FLT_EDS_mk_C_injective

/-! Proofs of the lemmas stated in `Theorems.Thm_EDS_PreDivisionAdjacentRelations` and their helpers. -/
open Polynomial WeierstrassCurve

open scoped Classical

namespace FLT.EDS

variable {R : Type*} [CommRing R]

/-- The adjacent Somos relation for the division polynomial `ψ`, in `R[X][Y]`.
Immediate from `normEDS_adjacent_somos` since `W.ψ n = normEDS W.ψ₂ (C Ψ₃) (C preΨ₄) n` (defn). -/
public lemma psi_adjacent_somos (W : WeierstrassCurve R) (m : ℤ) :
    W.ψ (m + 2) * W.ψ (m - 2)
      = W.ψ₂ ^ 2 * W.ψ (m + 1) * W.ψ (m - 1) - C W.Ψ₃ * W.ψ m ^ 2 := by
  simpa only [WeierstrassCurve.ψ] using
    normEDS_adjacent_somos W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) m

/-- Coordinate-ring form: under `mk`, `ψ₂² = Ψ₂Sq`, giving the Somos in terms of `Ψ₂Sq`. -/
public lemma mk_psi_adjacent_somos (W : WeierstrassCurve R) (m : ℤ) :
    Affine.CoordinateRing.mk W (W.ψ (m + 2)) * Affine.CoordinateRing.mk W (W.ψ (m - 2))
      = Affine.CoordinateRing.mk W (C W.Ψ₂Sq)
          * Affine.CoordinateRing.mk W (W.ψ (m + 1)) * Affine.CoordinateRing.mk W (W.ψ (m - 1))
        - Affine.CoordinateRing.mk W (C W.Ψ₃) * Affine.CoordinateRing.mk W (W.ψ m) ^ 2 := by
  have h := congrArg (Affine.CoordinateRing.mk W) (psi_adjacent_somos W m)
  simpa only [map_mul, map_sub, map_pow, Affine.CoordinateRing.mk_ψ₂_sq] using h

/-- preΨ adjacent Somos (the (m,2,1) instance), parity-dependent coefficient: even m → coeff 1,
odd m → coeff Ψ₂Sq². From `mk_psi_adjacent_somos` via `mk_psi_eq` (ψ₂ factors collapse through
`mk_ψ₂_sq`), descended by `mk_C_injective` + the `Ψ₂Sq ≠ 0` cancellation in the polynomial domain. -/
theorem _root_.solution [IsDomain R] (W : WeierstrassCurve R) (h4 : (4 : R) ≠ 0) (m : ℤ) :
    W.preΨ (m + 2) * W.preΨ (m - 2)
      = (if Even m then 1 else W.Ψ₂Sq ^ 2) * (W.preΨ (m + 1) * W.preΨ (m - 1))
        - W.Ψ₃ * W.preΨ m ^ 2 := by
  have hS := mk_psi_adjacent_somos W m
  rw [mk_psi_eq, mk_psi_eq, mk_psi_eq, mk_psi_eq, mk_psi_eq] at hS
  have h2sq := Affine.CoordinateRing.mk_ψ₂_sq W
  have ep2 : Even (m + 2) ↔ Even m := by simp [Int.even_add]
  have em2 : Even (m - 2) ↔ Even m := by simp [Int.even_sub]
  have ep1 : Even (m + 1) ↔ ¬ Even m := by rw [Int.even_add]; simp [Int.not_even_one]
  have em1 : Even (m - 1) ↔ ¬ Even m := by rw [Int.even_sub]; simp [Int.not_even_one]
  simp only [ep2, em2, ep1, em1] at hS
  by_cases hm : Even m
  · simp only [hm, if_true, not_true, if_false, mul_one] at hS
    rw [if_pos hm, one_mul]
    apply mul_left_cancel₀ (W.Ψ₂Sq_ne_zero h4)
    apply mk_C_injective W
    simp only [map_mul, map_sub, map_pow]
    rw [← h2sq] at hS ⊢
    linear_combination hS
  · simp only [hm, if_false, not_false_iff, if_true, mul_one] at hS
    rw [if_neg hm]
    apply mk_C_injective W
    simp only [map_mul, map_sub, map_pow]
    rw [← h2sq] at hS ⊢
    linear_combination hS

end FLT.EDS
