-- Prove2me | solution 1 for CurveSymmetry.familyInfinity_unit_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:36.4051+00:00
-- url     : https://prove2.me/submissions/b587d544-c8d2-4fd6-8880-13bef83a0737

-- Solution generated from lean/InfinityDifferentials.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma mem_familyInfinityPlace (x : QuadField (familyH m α)) :
    x ∈ familyInfinityPlace m α ↔
      familyInfinityMap m α x ∈ quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α) :=
  Iff.rfl
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution (e : QuadField (familyH m α)) :
    (e ∈ familyInfinityPlace m α ∧ e⁻¹ ∈ familyInfinityPlace m α) ↔
      (familyInfinityMap m α e ∈
          quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α) ∧
        (familyInfinityMap m α e)⁻¹ ∈
          quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)) := by
  constructor
  · rintro ⟨he, he'⟩
    refine ⟨(mem_familyInfinityPlace e).mp he, ?_⟩
    rw [← map_inv₀ (familyInfinityMap m α)]
    exact (mem_familyInfinityPlace _).mp he'
  · rintro ⟨he, he'⟩
    refine ⟨(mem_familyInfinityPlace e).mpr he, (mem_familyInfinityPlace _).mpr ?_⟩
    rw [map_inv₀ (familyInfinityMap m α)]
    exact he'
end

#print axioms solution
