-- Prove2me | solution 1 for CurveSymmetry.fermat_realLocus_infinite
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:01.027992+00:00
-- url     : https://prove2.me/submissions/69ece60b-760f-46a8-bdc6-720c1cec2b12

-- Solution generated from lean/Fermat.lean (curve-symmetry-lean): inlined helpers in
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
open Polynomial
theorem solution {d : ℕ} (hd : 0 < d) :
    (realLocus (fermatPolynomial d)).Infinite := by
  have hex : ∀ n : ℕ, ∃ z : ℂ, z ^ d = 1 + (n : ℂ) * Complex.I :=
    fun n => IsAlgClosed.exists_pow_nat_eq _ hd
  choose f hf using hex
  have hi : Function.Injective f := by
    intro n k h
    have he := congrArg (fun z : ℂ => z ^ d) h
    rw [hf, hf] at he
    have he' := congrArg Complex.im he
    simpa using he'
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨n, rfl⟩
  change MvPolynomial.eval _ (fermatPolynomial d) = 0
  rw [eval_fermat, hf]
  simp [star_add, star_mul]
  ring
end

#print axioms solution
