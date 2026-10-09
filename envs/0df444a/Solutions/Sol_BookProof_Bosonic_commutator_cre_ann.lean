-- Prove2me | solution 1 for BookProof.Bosonic.commutator_cre_ann
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:34:40.281662+00:00
-- url     : https://prove2.me/submissions/a1efb987-c1d1-4350-ab19-2bd1246dd8af

-- Generated from ChapterBosonicCCR.lean — solution of BookProof.Bosonic.commutator_cre_ann
import Mathlib
import Definitions.Def_ChapterBosonicCCR
import Theorems.Thm_BookProof_Bosonic_commutator_field_Jfield
open BookProof.Bosonic



open RealInnerProductSpace


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [Algebra ℝ R]
  [IsScalarTower ℝ ℂ R] [StarModule ℂ R]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [Algebra ℝ R]
  [IsScalarTower ℝ ℂ R] [StarModule ℂ R]
variable {J : V →ₗ[ℝ] V} {a : V →ₗ[ℝ] R}
omit [StarRing R] [Algebra ℂ R] [Algebra ℝ R] [IsScalarTower ℝ ℂ R] [StarModule ℂ R] in
/-- Expansion of the commutator of `x ∓ c·y` for a **central** element `c`:
`(x - c·y)(x + c·y) - (x + c·y)(x - c·y) = 2c·(x·y - y·x)`. -/
private theorem central_comm_expand {c x y : R} (hc : ∀ z : R, c * z = z * c) :
    (x - c * y) * (x + c * y) - (x + c * y) * (x - c * y) = (2 * c) * (x * y - y * x) := by
  have hcx : c * x = x * c := hc x
  have e1 : x * (c * y) = c * (x * y) := by rw [← mul_assoc, ← hcx, mul_assoc]
  have e2 : (c * y) * x = c * (y * x) := by rw [mul_assoc]
  noncomm_ring [e1, e2]

set_option maxHeartbeats 1000000 in
theorem solution (h : BosonicCCR J a) (hJsq : ∀ v, J (J v) = -v) (v : V) :
    cre a J v * ann a J v - ann a J v * cre a J v
      = algebraMap ℂ R ((2 * (‖v‖ ^ 2 : ℝ) : ℂ)) := by

  have key := commutator_field_Jfield h hJsq v
  simp only [cre, ann, Algebra.smul_def]
  rw [central_comm_expand (fun z => Algebra.commutes Complex.I z), key,
    show (2 : R) * algebraMap ℂ R Complex.I = algebraMap ℂ R (2 * Complex.I) by
      rw [map_mul, map_ofNat], ← map_mul]
  congr 1
  linear_combination (-2 * ((‖v‖ ^ 2 : ℝ) : ℂ)) * Complex.I_mul_I
