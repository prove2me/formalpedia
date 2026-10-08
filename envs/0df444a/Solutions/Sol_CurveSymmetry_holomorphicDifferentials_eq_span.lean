-- Prove2me | solution 1 for CurveSymmetry.holomorphicDifferentials_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:11:29.789141+00:00
-- url     : https://prove2.me/submissions/7190c40a-b871-40a9-af53-204ef8e6ed9c

-- Solution generated from lean/HolomorphicSpan.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Theorems.Thm_CurveSymmetry_holoBasisVec_mem
import Theorems.Thm_CurveSymmetry_holomorphic_coeff_form
import Theorems.Thm_CurveSymmetry_quad_kaehler_span_eq_top
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
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
section Quad
variable (h : ℂ[X]) [Fact (Irreducible (quadRat h))]
/-- Every differential is a multiple of `dt`. -/
theorem quad_exists_smul_D_t (ω : Ω[QuadField h⁄ℂ]) :
    ∃ c : QuadField h, ω = c • KaehlerDifferential.D ℂ (QuadField h) (quadT h) := by
  have hmem : ω ∈ Submodule.span (QuadField h)
      {KaehlerDifferential.D ℂ (QuadField h) (quadT h)} := by
    rw [quad_kaehler_span_eq_top]; trivial
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc.symm⟩
end Quad
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Infinity
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- A polynomial of degree less than `m`, divided by `w`, gives the corresponding combination
of the `tⁱ·dt/w`. -/
lemma poly_div_root_smul_dt (a : ℂ[X]) (ha : a.natDegree < m) :
    (algebraMap ℂ[X] (QuadField (familyH m α)) a * (AdjoinRoot.root (quadRat (familyH m α)))⁻¹) •
        KaehlerDifferential.D ℂ (QuadField (familyH m α)) (quadT (familyH m α)) =
      ∑ i : Fin m, a.coeff i • holoBasisVec m α i := by
  have hsum : a = ∑ i : Fin m, C (a.coeff i) * X ^ (i : ℕ) := by
    conv_lhs => rw [a.as_sum_range' m ha]
    rw [← Fin.sum_univ_eq_sum_range (fun i => (monomial i) (a.coeff i))]
    simp only [C_mul_X_pow_eq_monomial]
  have hC : ∀ z : ℂ, algebraMap ℂ[X] (QuadField (familyH m α)) (C z) =
      algebraMap ℂ (QuadField (familyH m α)) z := by
    intro z
    rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
  conv_lhs => rw [hsum]
  rw [map_sum, Finset.sum_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [holoBasisVec, holoCoeff, ← algebraMap_smul (QuadField (familyH m α)) (a.coeff i), smul_smul,
    map_mul, map_pow, hC, quadT, mul_assoc]
end Infinity
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution :
    holomorphicDifferentials m α =
      Submodule.span ℂ (Set.range fun i : Fin m => holoBasisVec m α i) := by
  refine le_antisymm ?_ ?_
  · intro ω hω
    obtain ⟨f, rfl⟩ := quad_exists_smul_D_t (familyH m α) ω
    obtain ⟨a, hadeg, rfl⟩ := holomorphic_coeff_form f hω
    rw [poly_div_root_smul_dt a hadeg]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact holoBasisVec_mem i i.2
end

#print axioms solution
