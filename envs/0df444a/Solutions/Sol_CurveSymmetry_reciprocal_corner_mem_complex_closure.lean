-- Prove2me | solution 1 for CurveSymmetry.reciprocal_corner_mem_complex_closure
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:01:27.549714+00:00
-- url     : https://prove2.me/submissions/1db07f81-c06d-494a-9ab3-302645112207

-- Solution generated from lean/ReciprocalCornerClosure.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_reciprocal_chart_complex_closure
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 0 < m) (α : ℂ) :
    affineSpectrumPoint ![0, 0] ∈
      closure (affineSpectrumPoint '' {v : Fin 2 → ℂ |
        eval v (familyInfinityPolynomial m α) = 0 ∧ v 0 ≠ 0 ∧ v 1 ≠ 0}) := by
  rw [reciprocal_chart_complex_closure hm α]
  intro f hf
  rcases Set.mem_singleton_iff.mp hf with rfl
  change eval ![0, 0] (familyInfinityPolynomial m α) = 0
  simp [familyInfinityPolynomial, fourTermForm, binaryForm, hm.ne']
end

#print axioms solution
