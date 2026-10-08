-- Prove2me | solution 1 for CurveSymmetry.quad_regular_points_coeff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:07:13.20919+00:00
-- url     : https://prove2.me/submissions/1390d75d-8e8c-4c18-9665-2239c106c613

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
import Theorems.Thm_CurveSymmetry_isRegularAt_ramified
import Theorems.Thm_CurveSymmetry_isRegularAt_unramified
import Theorems.Thm_CurveSymmetry_quadRing_isMaximal_iff
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
section Point
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- The root `w` lies in every point place's local ring. -/
lemma quadLocal_root_mem : AdjoinRoot.root (quadRat h) ∈ quadLocalRing h c d hd := by
  rw [← quadRingMap_root, ← algebraMap_quadRing_apply]
  exact Subalgebra.algebraMap_mem _ _
end Point
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Point
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
/-- An element of the function field lying in the local ring of every point place comes from
`ℂ[t][W]/(W² − h)`: that ring is the intersection of its localizations at maximal ideals. -/
theorem quad_mem_range_of_forall_local (g : QuadField h)
    (hg : ∀ (c d : ℂ) (hd : d ^ 2 = h.eval c), g ∈ quadLocalRing h c d hd) :
    ∃ y : QuadRing h, algebraMap (QuadRing h) (QuadField h) y = g := by
  have hbot := MaximalSpectrum.iInf_localization_eq_bot (QuadRing h) (QuadField h)
  have hmem : g ∈ (⊥ : Subalgebra (QuadRing h) (QuadField h)) := by
    rw [← hbot, Algebra.mem_iInf]
    rintro ⟨P, hP⟩
    obtain ⟨c, d, hd, rfl⟩ := (quadRing_isMaximal_iff h P).mp hP
    exact hg c d hd
  rw [Algebra.mem_bot] at hmem
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, hy⟩
end Point
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
theorem solution (f : QuadField h)
    (hreg : ∀ (c d : ℂ) (hd : d ^ 2 = h.eval c),
      IsRegularAt h c d hd (f • KaehlerDifferential.D ℂ (QuadField h) (quadT h))) :
    ∃ a b : ℂ[X], f * AdjoinRoot.root (quadRat h) =
      algebraMap ℂ[X] (QuadField h) a +
        algebraMap ℂ[X] (QuadField h) b * AdjoinRoot.root (quadRat h) := by
  have hlocal : ∀ (c d : ℂ) (hd : d ^ 2 = h.eval c),
      f * AdjoinRoot.root (quadRat h) ∈ quadLocalRing h c d hd := by
    intro c d hd
    by_cases hc : h.eval c = 0
    · exact (isRegularAt_ramified h c d hd hc f).mp (hreg c d hd)
    · exact Subalgebra.mul_mem _ ((isRegularAt_unramified h c d hd hc f).mp (hreg c d hd))
        (quadLocal_root_mem h c d hd)
  obtain ⟨y, hy⟩ := quad_mem_range_of_forall_local h _ hlocal
  obtain ⟨a, b, rfl⟩ := quadRing_exists_eq h y
  refine ⟨a, b, ?_⟩
  have hroot : algebraMap (QuadRing h) (QuadField h) (AdjoinRoot.root (quadPoly h)) =
      AdjoinRoot.root (quadRat h) := by
    rw [algebraMap_quadRing_apply, quadRingMap_root]
  rw [← hy, map_add, map_mul, hroot,
    ← IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h) (QuadField h),
    ← IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h) (QuadField h)]
end

#print axioms solution
