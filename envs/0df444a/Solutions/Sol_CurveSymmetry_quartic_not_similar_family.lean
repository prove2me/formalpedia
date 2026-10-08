-- Prove2me | solution 1 for CurveSymmetry.quartic_not_similar_family
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:15:36.832782+00:00
-- url     : https://prove2.me/submissions/94146ee7-75ed-4481-a5ee-634b8ac852f6

-- Solution generated from lean/QuarticComparison.lean (curve-symmetry-lean): inlined helpers in
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
import Theorems.Thm_CurveSymmetry_familyFunctionField_genus
import Theorems.Thm_CurveSymmetry_family_locus_eq
import Theorems.Thm_CurveSymmetry_family_point_of_norm
import Theorems.Thm_CurveSymmetry_fermat_realLocus_infinite
import Theorems.Thm_CurveSymmetry_genus_congr
import Theorems.Thm_CurveSymmetry_quarticHolo_linearIndependent
import Theorems.Thm_CurveSymmetry_quarticHolo_mem
import Theorems.Thm_CurveSymmetry_realLocus_fermat_four
import Theorems.Thm_CurveSymmetry_similarity_span_eq
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
open MvPolynomial
theorem family_realLocus_infinite {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    (realLocus (familyPolynomial m α)).Infinite := by
  have hex : ∀ n : ℕ, ∃ z ∈ realLocus (familyPolynomial m α), ‖z‖ = (n : ℝ) + 1 := by
    intro n
    exact family_point_of_norm hm ha (by positivity)
  choose f hf hnorm using hex
  have hinj : Function.Injective f := by
    intro n k h
    have he := congrArg norm h
    rw [hnorm, hnorm] at he
    exact_mod_cast (add_right_cancel he)
  exact (Set.infinite_range_of_injective hinj).mono (by rintro _ ⟨n, rfl⟩; exact hf n)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Fermat
/-- `ℂ[X, Y]/(X⁴ + Y⁴ − 2) ≅ ℂ[x][Y]/(Y⁴ − (2 − x⁴))`, through `toNested`. -/
noncomputable def fermatCoordinateRingEquiv :
    FermatCoordinateRing 4 ≃ₐ[ℂ] KummerRing 4 fermatQuartic :=
  Ideal.quotientEquivAlg (Ideal.span {fermatPolynomial 4})
    (Ideal.span {kummerPoly 4 fermatQuartic}) toNested (by
      rw [Ideal.map_span, Set.image_singleton]
      congr 2
      exact ((fermat_toNested 4).trans fermatNested_eq_kummerPoly).symm)
end Fermat
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Fermat
/-- **R01f**: the function field of `X⁴ + Y⁴ = 2` is the Kummer field of `y⁴ = 2 − x⁴`. -/
noncomputable def fermatFunctionFieldAlgEquiv :
    FermatFunctionField 4 ≃ₐ[ℂ] KummerField 4 fermatQuartic :=
  haveI := kummerRing_isFractionRing 4 fermatQuartic (by norm_num)
  IsFractionRing.algEquivOfAlgEquiv fermatCoordinateRingEquiv
end Fermat
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Similarity
/-- **R01f**: a direct similarity between the real loci of two irreducible equations with
infinite real loci gives an isomorphism of `ℂ`-algebras between their function fields. -/
noncomputable def similarityFunctionFieldEquiv {P Q : BPoly} (hP : Irreducible P)
    (hQ : Irreducible Q) (hPinf : (realLocus P).Infinite) (hQinf : (realLocus Q).Infinite)
    {a b : ℂ} (ha : a ≠ 0) (h : (fun z : ℂ => a * z + b) '' realLocus Q = realLocus P) :
    FractionRing (BPoly ⧸ Ideal.span {Q}) ≃ₐ[ℂ] FractionRing (BPoly ⧸ Ideal.span {P}) :=
  IsFractionRing.algEquivOfAlgEquiv
    (Ideal.quotientEquivAlg (Ideal.span {Q}) (Ideal.span {P}) (simPullEquiv a b ha).symm
      (similarity_span_eq hP hQ hPinf hQinf ha h))
end Similarity
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
/-- With finitely many holomorphic differentials, the quartic has at least three. -/
theorem quartic_three_le_genus [Module.Finite ℂ (holomorphicSpace K₄)] : 3 ≤ genus K₄ := by
  have hli : LinearIndependent ℂ
      (fun i : Fin 3 => (⟨quarticHolo i, quarticHolo_mem i⟩ : holomorphicSpace K₄)) :=
    LinearIndependent.of_comp (holomorphicSpace K₄).subtype quarticHolo_linearIndependent
  rw [genus]
  simpa using hli.fintype_card_le_finrank
end Quartic
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
local notation "K₄" => KummerField 4 fermatQuartic
theorem solution {α : ℂ} (hα : α ≠ star α) {a b : ℂ} (ha : a ≠ 0) :
    (fun z : ℂ => a * z + b) '' {z : ℂ | (z ^ 4).re = 1} ≠ extremalCurve 2 α := by
  intro hS
  have hm : Fact (0 < 2) := ⟨by norm_num⟩
  have hα' : Fact (α ≠ star α) := ⟨hα⟩
  rw [← realLocus_fermat_four, ← family_locus_eq] at hS
  let e : FermatFunctionField 4 ≃ₐ[ℂ] FamilyFunctionField 2 α :=
    similarityFunctionFieldEquiv (familyPolynomial_irreducible (by norm_num) hα)
      (fermat_irreducible (by norm_num)) (family_realLocus_infinite (by norm_num) hα)
      (fermat_realLocus_infinite (by norm_num)) ha hS
  have hg : genus K₄ = 2 :=
    (genus_congr (fermatFunctionFieldAlgEquiv.symm.trans e)).trans familyFunctionField_genus
  have hpos : 0 < Module.finrank ℂ (holomorphicSpace K₄) := by
    rw [show Module.finrank ℂ (holomorphicSpace K₄) = genus K₄ from rfl, hg]
    norm_num
  have hfin : Module.Finite ℂ (holomorphicSpace K₄) := Module.finite_of_finrank_pos hpos
  have := quartic_three_le_genus
  omega
end

#print axioms solution
