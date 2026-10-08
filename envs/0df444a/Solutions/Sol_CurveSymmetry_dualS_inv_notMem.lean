-- Prove2me | solution 1 for CurveSymmetry.dualS_inv_notMem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:30.624015+00:00
-- url     : https://prove2.me/submissions/f385abf7-047b-4729-8724-04bd34d4f1b8

-- Solution generated from lean/FermatInfinity.lean (curve-symmetry-lean): inlined helpers in
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
open Polynomial
local notation "K₄" => KummerField 4 fermatQuartic
local notation "K₄'" => KummerField 4 fermatDual
theorem solution : dualS⁻¹ ∉ dualLocalRing := by
  intro hmem
  set u := algebraMap (KummerRing 4 fermatDual) dualLocalRing (kummerShift 4 fermatDual 0)
  have hmax : u ∈ IsLocalRing.maximalIdeal dualLocalRing :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff dualLocalRing
      (RingHom.ker (kummerEval 4 fermatDual 0 fermatZeta fermatZeta_pow)) _).mpr
      (kummerShift_mem_ker 0 fermatZeta fermatZeta_pow)
  have hu : (u : K₄') = dualS := by
    show algebraMap (KummerRing 4 fermatDual) K₄' (kummerShift 4 fermatDual 0) = _
    rw [kummerShift, ← IsScalarTower.algebraMap_apply, C_0, sub_zero]
    rfl
  have h1 : u * ⟨dualS⁻¹, hmem⟩ = 1 := Subtype.ext (by
    change (u : K₄') * dualS⁻¹ = 1
    rw [hu, mul_inv_cancel₀ dualS_ne_zero])
  have hunit : IsUnit u := ⟨⟨u, ⟨dualS⁻¹, hmem⟩, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  exact (IsLocalRing.mem_maximalIdeal _).mp hmax hunit
end

#print axioms solution
