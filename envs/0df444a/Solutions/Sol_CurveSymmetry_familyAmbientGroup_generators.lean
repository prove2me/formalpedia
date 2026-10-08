-- Prove2me | solution 1 for CurveSymmetry.familyAmbientGroup_generators
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:07:08.627069+00:00
-- url     : https://prove2.me/submissions/8b00ca28-c0c4-43d5-9cde-0b9b22e0ab31

-- Solution generated from lean/FamilyDihedral.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Theorems.Thm_CurveSymmetry_familyAmbientGroup_dihedral
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

section
open CurveSymmetry
set_option autoImplicit false
open OnePoint
theorem solution {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) :
    ∃ r s : familyAmbientGroup m α,
      orderOf r = 2 * m ∧ orderOf s = 2 ∧ s * r * s = r⁻¹ ∧
      ∀ g, ∃ i : ℕ, i < 2 * m ∧ (g = r ^ i ∨ g = s * r ^ i) := by
  let : NeZero (2 * m) := ⟨by omega⟩
  obtain ⟨e⟩ := familyAmbientGroup_dihedral hm ha hα
  refine ⟨e (.r 1), e (.sr 0), ?_, ?_, ?_, ?_⟩
  · rw [e.orderOf_eq, DihedralGroup.orderOf_r_one]
  · rw [e.orderOf_eq, DihedralGroup.orderOf_sr]
  · rw [← map_mul, ← map_mul, ← map_inv]
    congr 1
    simp
  · intro g
    obtain ⟨x, rfl⟩ := e.surjective g
    cases x with
    | r i =>
      refine ⟨i.val, ZMod.val_lt i, Or.inl ?_⟩
      rw [← map_pow]
      congr 1
      simp
    | sr i =>
      refine ⟨i.val, ZMod.val_lt i, Or.inr ?_⟩
      rw [← map_pow, ← map_mul]
      congr 1
      simp
end

#print axioms solution
