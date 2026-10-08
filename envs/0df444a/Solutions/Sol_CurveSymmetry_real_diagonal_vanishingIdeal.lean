-- Prove2me | solution 1 for CurveSymmetry.real_diagonal_vanishingIdeal
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:51.630144+00:00
-- url     : https://prove2.me/submissions/9a69de6d-e7ce-4d4a-9185-2b2efde97270

-- Solution generated from lean/AffineClosure.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_dvd_of_realLocus_subset
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma mem_realLocus_eval_pair (P : BPoly) (z : ℂ) :
    z ∈ realLocus P ↔ eval ![z, star z] P = 0 := by
  have he : (fun i : Fin 2 => if i = 0 then z else star z) = ![z, star z] := by
    ext i
    fin_cases i <;> simp
  simp only [realLocus, Set.mem_ofPred_eq, he]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) :
    vanishingIdeal ℂ (affineRealDiagonal P) = Ideal.span {P} := by
  ext Q
  rw [Ideal.mem_span_singleton]
  constructor
  · intro hQ
    apply dvd_of_realLocus_subset hP hinf
    intro z hz
    apply (mem_realLocus_eval_pair Q z).mpr
    have he := (mem_vanishingIdeal_iff.mp hQ) ![z, star z] ⟨z, hz, rfl⟩
    simpa using he
  · rintro ⟨R, rfl⟩
    apply mem_vanishingIdeal_iff.mpr
    rintro _ ⟨z, hz, rfl⟩
    have he := (mem_realLocus_eval_pair P z).mp hz
    change eval ![z, star z] (P * R) = 0
    rw [map_mul, he, zero_mul]
end

#print axioms solution
