-- Prove2me | solution 1 for CurveSymmetry.isRegularAtInfinity_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:07:12.185296+00:00
-- url     : https://prove2.me/submissions/801227b5-c1a0-4eb6-8fd1-08f00d78abc9

-- Solution generated from lean/InfinityRegularity.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Theorems.Thm_CurveSymmetry_family_infinity_D_relation
import Theorems.Thm_CurveSymmetry_quad_derivative_ne_zero
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
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma familyInfinityMap_t :
    familyInfinityMap m α (algebraMap ℂ[X] (QuadField (familyH m α)) X) =
      (algebraMap ℂ[X] (QuadField (familyH m (star α))) X)⁻¹ := by
  rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField (familyH m α)),
    familyInfinityMap_of, RatFunc.algebraMap_X, ratInv_X, map_inv₀,
    IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField (familyH m (star α))),
    RatFunc.algebraMap_X]
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
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- The chart isomorphism sends `t` to `1/s`. -/
lemma familyInfinityAlgEquiv_quadT :
    familyInfinityAlgEquiv m α (quadT (familyH m α)) =
      (quadT (familyH m (star α)))⁻¹ := by
  rw [familyInfinityAlgEquiv_apply, quadT, familyInfinityMap_t, quadT]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma quadT_ne_zero (h : ℂ[X]) [Fact (Irreducible (quadRat h))] : quadT h ≠ 0 := by
  rw [quadT, IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h)]
  exact (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) (QuadField h)).injective).mpr
    (RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- The transport of `f·dt` is `φ(f)·d(1/s)`. -/
lemma kaehlerTransport_smul_D_quadT (f : QuadField (familyH m α)) :
    kaehlerTransport (familyInfinityAlgEquiv m α)
        (f • KaehlerDifferential.D ℂ (QuadField (familyH m α)) (quadT (familyH m α))) =
      familyInfinityMap m α f •
        KaehlerDifferential.D ℂ (QuadField (familyH m (star α)))
          (quadT (familyH m (star α)))⁻¹ := by
  rw [kaehlerTransport_smul, kaehlerTransport_D, familyInfinityAlgEquiv_quadT,
    familyInfinityAlgEquiv_apply]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution (f : QuadField (familyH m α)) :
    IsRegularAtInfinity (f • KaehlerDifferential.D ℂ (QuadField (familyH m α))
        (quadT (familyH m α))) ↔
      familyInfinityMap m α f *
          ((quadT (familyH m (star α)) ^ 2 *
            algebraMap ℂ[X] (QuadField (familyH m (star α)))
              (familyH m (star α)).derivative)⁻¹ *
            -(2 * AdjoinRoot.root (quadRat (familyH m (star α))))) ∈
        quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α) := by
  have hs := quadT_ne_zero (familyH m (star α))
  have hderiv := quad_derivative_ne_zero (familyH m (star α)) 0 (familyH_eval_zero m (star α))
  have hprod : quadT (familyH m (star α)) ^ 2 *
      algebraMap ℂ[X] (QuadField (familyH m (star α)))
        (familyH m (star α)).derivative ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hs) hderiv
  -- `d(1/s)` against the uniformizer `w'`
  have hD : KaehlerDifferential.D ℂ (QuadField (familyH m (star α)))
        (quadT (familyH m (star α)))⁻¹ =
      ((quadT (familyH m (star α)) ^ 2 *
          algebraMap ℂ[X] (QuadField (familyH m (star α)))
            (familyH m (star α)).derivative)⁻¹ *
          -(2 * AdjoinRoot.root (quadRat (familyH m (star α))))) •
        KaehlerDifferential.D ℂ (QuadField (familyH m (star α)))
          (AdjoinRoot.root (quadRat (familyH m (star α)))) := by
    have hrel := family_infinity_D_relation (m := m) (α := α)
    rw [familyInfinityAlgEquiv_quadT] at hrel
    conv_rhs => rw [← smul_smul, ← hrel, smul_smul, inv_mul_cancel₀ hprod, one_smul]
  rw [IsRegularAtInfinity, kaehlerTransport_smul_D_quadT, hD, smul_smul]
  exact isRegularAt_iff (familyH m (star α)) 0 0 (familyH_star_zero_point m α)
    (quad_ramified_uniformizer _ 0 0 (familyH_star_zero_point m α)
      (familyH_eval_zero m (star α)))
    (by rw [quad_ramified_uniformizer_coe])
end

#print axioms solution
