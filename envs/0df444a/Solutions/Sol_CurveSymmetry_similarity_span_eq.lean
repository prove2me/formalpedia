-- Prove2me | solution 1 for CurveSymmetry.similarity_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:54.710008+00:00
-- url     : https://prove2.me/submissions/1df31e22-ae83-4833-82c2-59ce90803598

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
import Theorems.Thm_CurveSymmetry_dvd_of_realLocus_subset
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
open Polynomial
section Similarity
lemma eval_simPull (a b z : ℂ) (P : BPoly) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) (simPull a b P) =
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then a * z + b else star (a * z + b)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [simPull]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, map_mul, map_mul, hP]
      congr 1
      fin_cases i <;> simp [simPull, star_add, star_mul, mul_comm]
end Similarity
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Similarity
lemma mem_realLocus_simPull (a b z : ℂ) (P : BPoly) :
    z ∈ realLocus (simPull a b P) ↔ a * z + b ∈ realLocus P := by
  change MvPolynomial.eval _ (simPull a b P) = 0 ↔ _
  rw [eval_simPull]
  rfl
end Similarity
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
theorem solution {P Q : BPoly} (hP : Irreducible P) (hQ : Irreducible Q)
    (hPinf : (realLocus P).Infinite) (hQinf : (realLocus Q).Infinite) {a b : ℂ} (ha : a ≠ 0)
    (h : (fun z : ℂ => a * z + b) '' realLocus Q = realLocus P) :
    Ideal.span {P} =
      (Ideal.span {Q}).map ((simPullEquiv a b ha).symm : BPoly →+* BPoly) := by
  have h1 : Q ∣ simPull a b P := dvd_of_realLocus_subset hQ hQinf fun z hz => by
    rw [mem_realLocus_simPull, ← h]
    exact ⟨z, hz, rfl⟩
  have h2 : P ∣ simPull a⁻¹ (-(a⁻¹ * b)) Q := dvd_of_realLocus_subset hP hPinf fun w hw => by
    rw [← h] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    rw [mem_realLocus_simPull]
    convert hz using 1
    field_simp
    ring
  have h3 : simPull a⁻¹ (-(a⁻¹ * b)) Q ∣ P := by
    have hmap := map_dvd (simPull a⁻¹ (-(a⁻¹ * b))) h1
    rwa [← AlgHom.comp_apply, simPull_comp, mul_inv_cancel₀ ha,
      show a * -(a⁻¹ * b) + b = 0 by field_simp; ring, simPull_one_zero,
      AlgHom.id_apply] at hmap
  rw [Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_eq_span_singleton.mpr (associated_of_dvd_dvd h2 h3)]
  rfl
end

#print axioms solution
