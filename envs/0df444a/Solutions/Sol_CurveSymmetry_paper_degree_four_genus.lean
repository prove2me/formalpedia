-- Prove2me | solution 1 for CurveSymmetry.paper_degree_four_genus
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:20:42.687002+00:00
-- url     : https://prove2.me/submissions/8116aa8e-d94e-4101-8b22-b65864492133

-- Solution generated from lean/PaperRemarks.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Definitions.Def_CurveSymmetry_10_KummerField
import Definitions.Def_CurveSymmetry_11_KummerLocal
import Definitions.Def_CurveSymmetry_12_FermatGenus
import Theorems.Thm_CurveSymmetry_fermatFunctionField_genus
import Theorems.Thm_CurveSymmetry_paper_degree_four_not_in_family
import Theorems.Thm_CurveSymmetry_paper_family_genus
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
import Mathlib.LinearAlgebra.Dimension.Finrank
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
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

section
open CurveSymmetry
set_option autoImplicit false
attribute [local instance] CurveSymmetry.fact_zero_lt_two
theorem solution :
    Nat.card (directIsometryGroup {z : ℂ | (z ^ 4).re = 1}) = 4 ∧
      genus (FermatFunctionField 4) = 3 ∧
      (∀ (α : ℂ) [Fact (α ≠ star α)], genus (FamilyFunctionField 2 α) = 2) ∧
      ¬ ∃ a b α : ℂ, a ≠ 0 ∧ α ≠ star α ∧
        ((fun z : ℂ => a * z + b) '' {z : ℂ | (z ^ 4).re = 1} = extremalCurve 2 α ∨
          (fun z : ℂ => a * star z + b) '' {z : ℂ | (z ^ 4).re = 1} = extremalCurve 2 α) := by
  obtain ⟨hcard, hnot⟩ := paper_degree_four_not_in_family
  exact ⟨hcard, fermatFunctionField_genus, fun _ _ => paper_family_genus, hnot⟩
end

#print axioms solution
