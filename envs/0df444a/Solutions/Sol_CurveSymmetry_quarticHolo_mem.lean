-- Prove2me | solution 1 for CurveSymmetry.quarticHolo_mem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:02:56.390003+00:00
-- url     : https://prove2.me/submissions/b177b965-ca3c-46d4-9b19-52c749d35603

-- Solution generated from lean/FermatHolomorphic.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Definitions.Def_CurveSymmetry_10_KummerField
import Theorems.Thm_CurveSymmetry_quartic_smul_dx_mem_holomorphicSpace
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
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
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
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quartic_polynomial_injective : Function.Injective (algebraMap ℂ[X] K₄) := by
  rw [IsScalarTower.algebraMap_eq ℂ[X] (RatFunc ℂ) K₄]
  exact (algebraMap (RatFunc ℂ) K₄).injective.comp (IsFractionRing.injective ℂ[X] (RatFunc ℂ))
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quarticX_ne_zero : quarticX ≠ 0 := by
  intro h0
  have : algebraMap ℂ[X] K₄ X = algebraMap ℂ[X] K₄ 0 := by
    rw [map_zero]
    exact h0
  exact X_ne_zero (quartic_polynomial_injective this)
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quarticY_ne_zero : quarticY ≠ 0 := by
  intro h0
  have h := kummerRoot_pow 4 fermatQuartic
  rw [show AdjoinRoot.root (kummerRat 4 fermatQuartic) = quarticY from rfl, h0,
    zero_pow (by norm_num)] at h
  have hf : (C 2 - X ^ 4 : ℂ[X]) = 0 := quartic_polynomial_injective (by rw [map_zero]; exact h.symm)
  have := congrArg (eval 0) hf
  simp at this
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
/-- Holomorphy of `P·dx/y³` from the membership of the numerator `P` at the places. -/
lemma quartic_num_mem {P : K₄}
    (hP1 : ∀ O : ValuationSubring K₄, quarticX ∈ O → quarticY ∈ O → P ∈ O)
    (hP3 : ∀ O : ValuationSubring K₄, quarticX⁻¹ ∈ O → quarticX * quarticY⁻¹ ∈ O →
      P * quarticY⁻¹ ^ 3 * quarticX ^ 2 ∈ O) :
    (P * quarticY⁻¹ ^ 3) • KaehlerDifferential.D ℂ K₄ quarticX ∈ holomorphicSpace K₄ := by
  have hx0 := quarticX_ne_zero
  have hy0 := quarticY_ne_zero
  apply quartic_smul_dx_mem_holomorphicSpace
  · intro O hx hy hyi
    exact mul_mem (hP1 O hx hy) (pow_mem hyi 3)
  · intro O hx hxi hy
    rw [show P * quarticY⁻¹ ^ 3 * quarticY ^ 3 * quarticX⁻¹ ^ 3 = P * quarticX⁻¹ ^ 3 by
      field_simp]
    exact mul_mem (hP1 O hx hy) (pow_mem hxi 3)
  · exact hP3
end Quartic
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
local notation "K₄" => KummerField 4 fermatQuartic
theorem solution (i : Fin 3) : quarticHolo i ∈ holomorphicSpace K₄ := by
  have hx0 := quarticX_ne_zero
  have hy0 := quarticY_ne_zero
  fin_cases i
  · show ((1 : K₄) * quarticY⁻¹ ^ 3) • KaehlerDifferential.D ℂ K₄ quarticX ∈ _
    refine quartic_num_mem (fun O _ _ => one_mem O) fun O hxi hr => ?_
    rw [show (1 : K₄) * quarticY⁻¹ ^ 3 * quarticX ^ 2 =
      quarticX⁻¹ * (quarticX * quarticY⁻¹) ^ 3 by field_simp]
    exact mul_mem hxi (pow_mem hr 3)
  · show (quarticX * quarticY⁻¹ ^ 3) • KaehlerDifferential.D ℂ K₄ quarticX ∈ _
    refine quartic_num_mem (fun O hx _ => hx) fun O _ hr => ?_
    rw [show quarticX * quarticY⁻¹ ^ 3 * quarticX ^ 2 = (quarticX * quarticY⁻¹) ^ 3 by
      field_simp]
    exact pow_mem hr 3
  · show (quarticY * quarticY⁻¹ ^ 3) • KaehlerDifferential.D ℂ K₄ quarticX ∈ _
    refine quartic_num_mem (fun O _ hy => hy) fun O _ hr => ?_
    rw [show quarticY * quarticY⁻¹ ^ 3 * quarticX ^ 2 = (quarticX * quarticY⁻¹) ^ 2 by
      field_simp]
    exact pow_mem hr 2
end

#print axioms solution
