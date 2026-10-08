-- Prove2me | solution 1 for CurveSymmetry.mem_regularAt_quadPlace_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:37.297995+00:00
-- url     : https://prove2.me/submissions/7874422c-b3fb-40a6-bdd6-4ddac8167dbd

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
import Theorems.Thm_CurveSymmetry_mem_regularAt_iff_of_generator
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
section Genus
variable {K : Type*} [Field K] [Algebra ℂ K]
/-- A generator of the differentials of a ring `A` inside `K` gives the generator condition of
`mem_regularAt_iff_of_generator` for the elements of `A`. -/
theorem exists_D_eq_smul_of_span_eq_top {A : Type*} [CommRing A] [Algebra ℂ A] [Algebra A K]
    [IsScalarTower ℂ A K] {u : A}
    (hu : Submodule.span A {KaehlerDifferential.D ℂ A u} = ⊤) (b : A) :
    ∃ g : A, KaehlerDifferential.D ℂ K (algebraMap A K b) =
      algebraMap A K g • KaehlerDifferential.D ℂ K (algebraMap A K u) := by
  have hb : KaehlerDifferential.D ℂ A b ∈ Submodule.span A {KaehlerDifferential.D ℂ A u} := by
    rw [hu]; trivial
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp hb
  refine ⟨g, ?_⟩
  have hmap := congrArg (KaehlerDifferential.map ℂ ℂ A K) hg
  rw [map_smul, KaehlerDifferential.map_D, KaehlerDifferential.map_D] at hmap
  rw [← hmap, IsScalarTower.algebraMap_smul]
end Genus
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
theorem solution (ω : Ω[QuadField h⁄ℂ]) :
    ω ∈ regularAt (quadPlace h c d hd) ↔ IsRegularAt h c d hd ω := by
  obtain ⟨u, hu, hspan⟩ := quadLocal_exists_uniformizer h c d hd
  obtain ⟨f, hf⟩ := quadLocal_exists_coeff h c d hd hu ω
  have hgen : ∀ b ∈ quadPlace h c d hd, ∃ g ∈ quadPlace h c d hd,
      KaehlerDifferential.D ℂ (QuadField h) b =
        g • KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h) := by
    intro b hb
    obtain ⟨g, hg⟩ := exists_D_eq_smul_of_span_eq_top (K := QuadField h) hspan ⟨b, hb⟩
    exact ⟨g, g.2, hg⟩
  rw [mem_regularAt_iff_of_generator u.2 (quadLocal_const_mem h c d hd) hgen,
    isRegularAt_iff h c d hd hu hf]
  constructor
  · rintro ⟨f', hf', hω⟩
    have hdu := quadLocal_D_uniformizer_ne_zero h c d hd hu
    have hsub : (f - f') • KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h) = 0 := by
      rw [sub_smul, ← hf, ← hω, sub_self]
    rcases smul_eq_zero.mp hsub with h0 | h0
    · rw [sub_eq_zero.mp h0]
      exact hf'
    · exact absurd h0 hdu
  · intro hfmem
    exact ⟨f, hfmem, hf⟩
end

#print axioms solution
