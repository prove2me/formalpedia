-- Prove2me | solution 1 for CurveSymmetry.family_infinity_D_relation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:05:52.969984+00:00
-- url     : https://prove2.me/submissions/84b25143-52b4-4ab3-b346-3ed1449f5859

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
import Theorems.Thm_CurveSymmetry_quad_ramified_coeff
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

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution :
    (quadT (familyH m (star α)) ^ 2 *
          algebraMap ℂ[X] (QuadField (familyH m (star α))) (familyH m (star α)).derivative) •
        KaehlerDifferential.D ℂ (QuadField (familyH m (star α)))
          (familyInfinityAlgEquiv m α (quadT (familyH m α))) =
      (-(2 * AdjoinRoot.root (quadRat (familyH m (star α))))) •
        KaehlerDifferential.D ℂ (QuadField (familyH m (star α)))
          (AdjoinRoot.root (quadRat (familyH m (star α)))) := by
  have hs := quadT_ne_zero (familyH m (star α))
  have h2f := quad_ramified_coeff (familyH m (star α)) 1
  rw [one_smul] at h2f
  rw [familyInfinityAlgEquiv_quadT, Derivation.leibniz_inv, smul_smul]
  have hcoef : quadT (familyH m (star α)) ^ 2 *
      algebraMap ℂ[X] (QuadField (familyH m (star α))) (familyH m (star α)).derivative *
        -(quadT (familyH m (star α)))⁻¹ ^ 2 =
      -(algebraMap ℂ[X] (QuadField (familyH m (star α))) (familyH m (star α)).derivative) := by
    field_simp
  rw [hcoef, neg_smul, h2f, ← neg_smul]
  congr 1
  ring
end

#print axioms solution
