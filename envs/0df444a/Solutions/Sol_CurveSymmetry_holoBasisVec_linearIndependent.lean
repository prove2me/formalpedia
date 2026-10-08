-- Prove2me | solution 1 for CurveSymmetry.holoBasisVec_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:06.253501+00:00
-- url     : https://prove2.me/submissions/816aa2d6-12be-40e5-9b93-7df46cf81b46

-- Solution generated from lean/HolomorphicBasis.lean (curve-symmetry-lean): inlined helpers in
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
open Polynomial TensorProduct
section BaseChange
variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T] [Algebra.FormallyEtale S T] {ι : Type*} [Unique ι]
omit [Unique ι] in
@[simp] lemma kaehlerBasisOfEtale_apply (b : Module.Basis ι S Ω[S⁄R]) (i : ι) :
    kaehlerBasisOfEtale R S T b i = KaehlerDifferential.map R R S T (b i) := by
  simp [kaehlerBasisOfEtale, Module.Basis.baseChange_apply,
    KaehlerDifferential.mapBaseChange_tmul]
end BaseChange
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
@[simp] lemma polynomialKaehlerBasis_apply (i : Unit) :
    polynomialKaehlerBasis i = KaehlerDifferential.D ℂ ℂ[X] X := by
  simp [polynomialKaehlerBasis, Module.Basis.singleton_apply,
    KaehlerDifferential.polynomialEquiv_symm]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
@[simp] lemma ratFuncKaehlerBasis_apply (i : Unit) :
    ratFuncKaehlerBasis i = KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X := by
  rw [ratFuncKaehlerBasis, kaehlerBasisOfEtale_apply, polynomialKaehlerBasis_apply,
    KaehlerDifferential.map_D, RatFunc.algebraMap_X]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
section Quad
variable (h : ℂ[X]) [Fact (Irreducible (quadRat h))]
lemma quadT_eq : quadT h = algebraMap (RatFunc ℂ) (QuadField h) RatFunc.X := by
  rw [quadT, IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h), RatFunc.algebraMap_X]
end Quad
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
section Quad
variable (h : ℂ[X]) [Fact (Irreducible (quadRat h))]
@[simp] lemma quadKaehlerBasis_apply (i : Unit) :
    quadKaehlerBasis h i = KaehlerDifferential.D ℂ (QuadField h) (quadT h) := by
  rw [quadKaehlerBasis, kaehlerBasisOfEtale_apply, ratFuncKaehlerBasis_apply,
    KaehlerDifferential.map_D, quadT_eq]
end Quad
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
section Quad
variable (h : ℂ[X]) [Fact (Irreducible (quadRat h))]
theorem quad_D_t_ne_zero : KaehlerDifferential.D ℂ (QuadField h) (quadT h) ≠ 0 := by
  have := (quadKaehlerBasis h).ne_zero (default : Unit)
  rwa [quadKaehlerBasis_apply] at this
end Quad
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- The root `w` is nonzero in the function field: `w² = h ≠ 0`. -/
lemma quadRoot_ne_zero : AdjoinRoot.root (quadRat h) ≠ 0 := by
  intro hzero
  have hsq := quadRoot_sq h
  rw [hzero, zero_pow two_ne_zero] at hsq
  have hne : algebraMap (RatFunc ℂ) (QuadField h) (algebraMap ℂ[X] (RatFunc ℂ) h) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) (QuadField h)).injective).mpr
      (RatFunc.algebraMap_ne_zero (Fact.out : Squarefree h).ne_zero)
  exact hne hsq.symm
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- Polynomials in `t` embed injectively into the function field. -/
lemma algebraMap_polynomial_injective :
    Function.Injective (algebraMap ℂ[X] (QuadField (familyH m α))) := by
  rw [IsScalarTower.algebraMap_eq ℂ[X] (RatFunc ℂ) (QuadField (familyH m α))]
  exact (algebraMap (RatFunc ℂ) (QuadField (familyH m α))).injective.comp
    (IsFractionRing.injective ℂ[X] (RatFunc ℂ))
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution :
    LinearIndependent ℂ (fun i : Fin m => holoBasisVec m α i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hw := quadRoot_ne_zero (familyH m α)
  have hdt := quad_D_t_ne_zero (familyH m α)
  -- collect the coefficients into one polynomial
  set p : ℂ[X] := ∑ i : Fin m, C (g i) * X ^ (i : ℕ) with hp
  have hC : ∀ z : ℂ, algebraMap ℂ[X] (QuadField (familyH m α)) (C z) =
      algebraMap ℂ (QuadField (familyH m α)) z := by
    intro z
    rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
  have hterm : ∀ i : Fin m, g i • holoBasisVec m α i =
      (algebraMap ℂ[X] (QuadField (familyH m α)) (C (g i) * X ^ (i : ℕ)) *
          (AdjoinRoot.root (quadRat (familyH m α)))⁻¹) •
        KaehlerDifferential.D ℂ (QuadField (familyH m α)) (quadT (familyH m α)) := by
    intro i
    rw [holoBasisVec, holoCoeff, ← algebraMap_smul (QuadField (familyH m α)) (g i), smul_smul,
      map_mul, map_pow, hC, quadT, mul_assoc]
  have hsum : ∑ i : Fin m, g i • holoBasisVec m α i =
      (algebraMap ℂ[X] (QuadField (familyH m α)) p *
          (AdjoinRoot.root (quadRat (familyH m α)))⁻¹) •
        KaehlerDifferential.D ℂ (QuadField (familyH m α)) (quadT (familyH m α)) := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_smul, ← Finset.sum_mul, hp,
      map_sum]
  rw [hsum] at hg
  rcases smul_eq_zero.mp hg with hzero | hzero
  · have hpzero : algebraMap ℂ[X] (QuadField (familyH m α)) p = 0 := by
      rcases mul_eq_zero.mp hzero with h0 | h0
      · exact h0
      · exact absurd (inv_eq_zero.mp h0) hw
    have hp0 : p = 0 := algebraMap_polynomial_injective (by rw [hpzero, map_zero])
    intro i
    have hcoeff := congrArg (fun q : ℂ[X] => q.coeff i) hp0
    simp only [hp, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hcoeff
    rw [Finset.sum_eq_single i (fun b _ hb => by
      rw [if_neg (fun h' => hb (Fin.ext h'.symm)), mul_zero]) (by simp)] at hcoeff
    simpa using hcoeff
  · exact absurd hzero hdt
end

#print axioms solution
