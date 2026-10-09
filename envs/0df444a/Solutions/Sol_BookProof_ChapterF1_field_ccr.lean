-- Prove2me | solution 1 for BookProof.ChapterF1.field_ccr
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:55:36.719663+00:00
-- url     : https://prove2.me/submissions/ae371b1a-53f7-444a-a3d6-ea8bbf3f21dd

-- Generated from ChapterF1.lean — solution of BookProof.ChapterF1.field_ccr
import Mathlib
import Definitions.Def_ChapterF1
open BookProof.ChapterF1



open Polynomial Finset
open scoped BigOperators


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution :
    fieldPhi ∘ₗ fieldPi - fieldPi ∘ₗ fieldPhi = (2 * Complex.I) • LinearMap.id := by

  ext p
  unfold fieldPhi fieldPi
  simp [← mul_assoc, ← Polynomial.C_mul_X_pow_eq_monomial,
    Polynomial.coeff_X_pow, mul_sub, mul_add,
    mul_comm, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.sub_apply]
  split_ifs <;> ring
