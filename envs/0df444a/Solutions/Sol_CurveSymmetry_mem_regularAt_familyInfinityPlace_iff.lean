-- Prove2me | solution 1 for CurveSymmetry.mem_regularAt_familyInfinityPlace_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:02:50.926252+00:00
-- url     : https://prove2.me/submissions/ce0c22b2-e2c8-46d3-b90f-acec7cd80943

-- Solution generated from lean/FamilyGenus.lean (curve-symmetry-lean): inlined helpers in
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
import Theorems.Thm_CurveSymmetry_familyInfinityPlace_eq_comap
import Theorems.Thm_CurveSymmetry_mem_regularAt_quadPlace_iff
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
section Transport
variable {K L : Type*} [Field K] [Algebra ℂ K] [Field L] [Algebra ℂ L]
/-- Regularity at a pulled-back place is regularity of the transported differential. -/
theorem mem_regularAt_comap_iff (e : K ≃ₐ[ℂ] L) (O : ValuationSubring L) (ω : Ω[K⁄ℂ]) :
    ω ∈ regularAt (O.comap (e : K →+* L)) ↔ kaehlerTransport e ω ∈ regularAt O := by
  refine ⟨kaehlerTransport_mem_regularAt e O, fun hω => ?_⟩
  have hO : (O.comap (e : K →+* L)).comap (e.symm : L →+* K) = O := by
    ext y
    simp [ValuationSubring.mem_comap]
  rw [← hO] at hω
  have hback := kaehlerTransport_mem_regularAt e.symm (O.comap (e : K →+* L)) hω
  rwa [kaehlerTransport_symm_apply] at hback
end Transport
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution (ω : Ω[QuadField (familyH m α)⁄ℂ]) :
    ω ∈ regularAt (familyInfinityPlace m α) ↔ IsRegularAtInfinity ω := by
  rw [familyInfinityPlace_eq_comap, mem_regularAt_comap_iff, mem_regularAt_quadPlace_iff]
  rfl
end

#print axioms solution
