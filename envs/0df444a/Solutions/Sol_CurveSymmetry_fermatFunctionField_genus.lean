-- Prove2me | solution 1 for CurveSymmetry.fermatFunctionField_genus
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:11:29.07406+00:00
-- url     : https://prove2.me/submissions/60e48b78-ea00-4383-afdf-f02ba3c13729

-- Solution generated from lean/FermatGenus.lean (curve-symmetry-lean): inlined helpers in
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
import Theorems.Thm_CurveSymmetry_genus_congr
import Theorems.Thm_CurveSymmetry_quartic_genus
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

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Fermat
/-- `ℂ[X, Y]/(X⁴ + Y⁴ − 2) ≅ ℂ[x][Y]/(Y⁴ − (2 − x⁴))`, through `toNested`. -/
noncomputable def fermatCoordinateRingEquiv :
    FermatCoordinateRing 4 ≃ₐ[ℂ] KummerRing 4 fermatQuartic :=
  Ideal.quotientEquivAlg (Ideal.span {fermatPolynomial 4})
    (Ideal.span {kummerPoly 4 fermatQuartic}) toNested (by
      rw [Ideal.map_span, Set.image_singleton]
      congr 2
      exact ((fermat_toNested 4).trans fermatNested_eq_kummerPoly).symm)
end Fermat
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Fermat
/-- **R01f**: the function field of `X⁴ + Y⁴ = 2` is the Kummer field of `y⁴ = 2 − x⁴`. -/
noncomputable def fermatFunctionFieldAlgEquiv :
    FermatFunctionField 4 ≃ₐ[ℂ] KummerField 4 fermatQuartic :=
  haveI := kummerRing_isFractionRing 4 fermatQuartic (by norm_num)
  IsFractionRing.algEquivOfAlgEquiv fermatCoordinateRingEquiv
end Fermat
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
theorem solution : genus (FermatFunctionField 4) = 3 :=
  (genus_congr fermatFunctionFieldAlgEquiv).trans quartic_genus
end

#print axioms solution
