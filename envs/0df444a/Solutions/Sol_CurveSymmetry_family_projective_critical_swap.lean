-- Prove2me | solution 1 for CurveSymmetry.family_projective_critical_swap
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:31.331073+00:00
-- url     : https://prove2.me/submissions/c785743e-f81b-4c39-a6b7-9bd897dc086d

-- Solution generated from lean/HomogeneousDifferential.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_criticalZero_transport
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma familyBihomogeneous_swap (m : ℕ) (α : ℂ) (x y : Fin 2 → ℂ) :
    familyBihomogeneous m α y x = familyBihomogeneous m (star α) x y := by
  simp only [familyBihomogeneous, star_star]
  ring
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
theorem solution (m : ℕ) (α : ℂ)
    (p : ProjectiveLine × ProjectiveLine) :
    p.swap ∈ familyProjectiveCritical m α ↔ p ∈ familyProjectiveCritical m (star α) := by
  let T : HomogeneousPairs ≃L[ℂ] HomogeneousPairs :=
    (LinearEquiv.prodComm ℂ (Fin 2 → ℂ) (Fin 2 → ℂ)).toContinuousLinearEquiv
  have he (q : HomogeneousPairs) :
      familyBihomogeneous m α (T q).1 (T q).2 =
        1 * familyBihomogeneous m (star α) q.1 q.2 := by
    change familyBihomogeneous m α q.2 q.1 = _
    rw [familyBihomogeneous_swap, one_mul]
  convert criticalZero_transport T (k := (1 : ℂ))
    (F := fun q : HomogeneousPairs => familyBihomogeneous m (star α) q.1 q.2)
    (G := fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2)
    one_ne_zero he (p.1.rep, p.2.rep) using 1 <;> rfl
end

#print axioms solution
