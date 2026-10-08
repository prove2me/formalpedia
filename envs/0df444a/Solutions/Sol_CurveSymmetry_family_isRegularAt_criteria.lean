-- Prove2me | solution 1 for CurveSymmetry.family_isRegularAt_criteria
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:07:09.437984+00:00
-- url     : https://prove2.me/submissions/0645a888-5a6e-4036-876b-a98a16edd36b

-- Solution generated from lean/HolomorphicDifferentials.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Theorems.Thm_CurveSymmetry_isRegularAt_ramified
import Theorems.Thm_CurveSymmetry_isRegularAt_unramified
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

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c)
    (f : QuadField (familyH m α)) :
    ((familyH m α).eval c ≠ 0 →
        (IsRegularAt (familyH m α) c d hd
            (f • KaehlerDifferential.D ℂ (QuadField (familyH m α)) (quadT (familyH m α))) ↔
          f ∈ quadLocalRing (familyH m α) c d hd)) ∧
      ((familyH m α).eval c = 0 →
        (IsRegularAt (familyH m α) c d hd
            (f • KaehlerDifferential.D ℂ (QuadField (familyH m α)) (quadT (familyH m α))) ↔
          f * AdjoinRoot.root (quadRat (familyH m α)) ∈ quadLocalRing (familyH m α) c d hd)) :=
  ⟨fun hc => isRegularAt_unramified _ c d hd hc f,
    fun hc => isRegularAt_ramified _ c d hd hc f⟩
end

#print axioms solution
