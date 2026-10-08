-- Prove2me | solution 1 for CurveSymmetry.fermat_not_circle
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:00.129675+00:00
-- url     : https://prove2.me/submissions/996768e8-67a8-4536-ba32-1a7027c13b0d

-- Solution generated from lean/Sharpness.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
lemma eval_fermat (d : ℕ) (z : ℂ) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) (fermatPolynomial d) =
      z ^ d + star (z ^ d) - 2 := by
  simp [fermatPolynomial, star_pow]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
theorem solution {d : ℕ} (hd : 0 < d) : NotCircle (fermatPolynomial d) := by
  rintro ⟨c, R, hR, he⟩
  let t : ℝ := (‖c‖ + R) ^ d + 1
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (1 + (t : ℂ) * Complex.I) hd
  have hmem : z ∈ realLocus (fermatPolynomial d) := by
    change MvPolynomial.eval _ (fermatPolynomial d) = 0
    rw [eval_fermat, hz]
    simp [star_add, star_mul]
    ring
  rw [he, Metric.mem_sphere, dist_eq_norm] at hmem
  have hb := norm_add_le (z - c) c
  rw [sub_add_cancel, hmem] at hb
  have hpow := pow_le_pow_left₀ (norm_nonneg z) hb d
  have him := Complex.abs_im_le_norm (z ^ d)
  have him' : (z ^ d).im = t := by rw [hz]; simp
  rw [him', abs_of_pos ht, norm_pow] at him
  dsimp [t] at him
  have he' : R + ‖c‖ = ‖c‖ + R := add_comm _ _
  rw [he'] at hpow
  linarith
end

#print axioms solution
