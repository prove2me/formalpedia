-- Prove2me | solution 1 for CurveSymmetry.isRegularAt_ramified
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:05:56.206976+00:00
-- url     : https://prove2.me/submissions/4da0fc33-0451-4188-8fd7-b038c102c56d

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
import Theorems.Thm_CurveSymmetry_quad_derivative_ne_zero
import Theorems.Thm_CurveSymmetry_quad_ramified_coeff
import Theorems.Thm_CurveSymmetry_quad_ramified_derivative_isUnit
import Theorems.Thm_CurveSymmetry_quad_ramified_uniformizer
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
section
variable (h : ℂ[X])
lemma algebraMap_quadRing_apply (y : QuadRing h) :
    algebraMap (QuadRing h) (QuadField h) y = quadRingMap h y := rfl
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- The image of that uniformizer in the function field is the root `w`. -/
theorem quad_ramified_uniformizer_coe :
    ((algebraMap (QuadRing h) (quadLocalRing h c d hd) (AdjoinRoot.root (quadPoly h)) :
        quadLocalRing h c d hd) : QuadField h) = AdjoinRoot.root (quadRat h) := by
  show algebraMap (QuadRing h) (QuadField h) (AdjoinRoot.root (quadPoly h)) = _
  rw [algebraMap_quadRing_apply, quadRingMap_root]
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- An element that becomes a unit of the local ring has its inverse there. -/
lemma quadLocal_inv_mem_of_isUnit {x : QuadRing h}
    (hx : IsUnit (algebraMap (QuadRing h) (quadLocalRing h c d hd) x)) :
    (algebraMap (QuadRing h) (QuadField h) x)⁻¹ ∈ quadLocalRing h c d hd := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have hcoe : algebraMap (QuadRing h) (QuadField h) x * (y : QuadField h) = 1 := by
    have hc1 := congrArg (fun z : quadLocalRing h c d hd => (z : QuadField h)) hy
    simpa using hc1
  rw [inv_eq_of_mul_eq_one_right hcoe]
  exact y.2
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
theorem solution (hc : h.eval c = 0) (f : QuadField h) :
    IsRegularAt h c d hd (f • KaehlerDifferential.D ℂ (QuadField h) (quadT h)) ↔
      f * AdjoinRoot.root (quadRat h) ∈ quadLocalRing h c d hd := by
  have hderiv := quad_derivative_ne_zero h c hc
  have hrel := quad_ramified_coeff h f
  have hcoeff : f • KaehlerDifferential.D ℂ (QuadField h) (quadT h) =
      ((algebraMap ℂ[X] (QuadField h) h.derivative)⁻¹ *
          (2 * f * AdjoinRoot.root (quadRat h))) •
        KaehlerDifferential.D ℂ (QuadField h) (AdjoinRoot.root (quadRat h)) := by
    conv_rhs => rw [← smul_smul, ← hrel, smul_smul, inv_mul_cancel₀ hderiv, one_smul]
  rw [isRegularAt_iff h c d hd (quad_ramified_uniformizer h c d hd hc)
    (by rw [quad_ramified_uniformizer_coe]; exact hcoeff)]
  have htower : algebraMap ℂ[X] (QuadField h) h.derivative =
      algebraMap (QuadRing h) (QuadField h)
        (algebraMap ℂ[X] (QuadRing h) h.derivative) := by
    rw [← IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h) (QuadField h)]
  have hpmem : algebraMap ℂ[X] (QuadField h) h.derivative ∈ quadLocalRing h c d hd := by
    rw [htower]
    exact Subalgebra.algebraMap_mem _ _
  have hinvmem : (algebraMap ℂ[X] (QuadField h) h.derivative)⁻¹ ∈
      quadLocalRing h c d hd := by
    rw [htower]
    exact quadLocal_inv_mem_of_isUnit h c d hd (quad_ramified_derivative_isUnit h c d hd hc)
  have htwo : (2 : QuadField h) = algebraMap ℂ (QuadField h) 2 :=
    (map_ofNat (algebraMap ℂ (QuadField h)) 2).symm
  have htwoinv : (2 : QuadField h)⁻¹ = algebraMap ℂ (QuadField h) 2⁻¹ := by
    rw [htwo, ← map_inv₀]
  constructor
  · intro hmem
    have hfac : f * AdjoinRoot.root (quadRat h) =
        (algebraMap ℂ[X] (QuadField h) h.derivative * 2⁻¹) *
          ((algebraMap ℂ[X] (QuadField h) h.derivative)⁻¹ *
            (2 * f * AdjoinRoot.root (quadRat h))) := by
      field_simp
    rw [hfac]
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hpmem ?_) hmem
    rw [htwoinv]
    exact quadLocal_const_mem h c d hd _
  · intro hmem
    have hfac : (algebraMap ℂ[X] (QuadField h) h.derivative)⁻¹ *
        (2 * f * AdjoinRoot.root (quadRat h)) =
        ((algebraMap ℂ[X] (QuadField h) h.derivative)⁻¹ * 2) *
          (f * AdjoinRoot.root (quadRat h)) := by
      ring
    rw [hfac]
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hinvmem ?_) hmem
    rw [htwo]
    exact quadLocal_const_mem h c d hd _
end

#print axioms solution
