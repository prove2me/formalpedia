-- Prove2me | solution 1 for CurveSymmetry.paper_degree_four_not_in_family
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:18:40.808976+00:00
-- url     : https://prove2.me/submissions/2aaaef8e-665d-48e6-ae62-8c286f73df8e

-- Solution generated from lean/PaperRemarks.lean (curve-symmetry-lean): inlined helpers in
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
import Definitions.Def_CurveSymmetry_11_KummerLocal
import Definitions.Def_CurveSymmetry_12_FermatGenus
import Theorems.Thm_CurveSymmetry_fermat_direct_card
import Theorems.Thm_CurveSymmetry_quartic_not_oppositeSimilar_family
import Theorems.Thm_CurveSymmetry_quartic_not_similar_family
import Theorems.Thm_CurveSymmetry_realLocus_fermat_four
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
lemma direct_parameters_unique {a b c d : ℂ}
    (h : ∀ z : ℂ, a * z + b = c * z + d) : (a, b) = (c, d) := by
  have h0 := h 0
  have h1 := h 1
  simp only [mul_zero, zero_add] at h0
  simp only [mul_one] at h1
  apply Prod.ext
  · linear_combination h1 - h0
  · exact h0
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma directParametersToIsometry_bijective (P : BPoly) :
    Function.Bijective (directParametersToIsometry P) := by
  constructor
  · intro u v he
    apply Subtype.ext
    apply direct_parameters_unique
    intro z
    exact congrArg (fun f : directIsometryGroup (realLocus P) => f.val z) he
  · rintro ⟨f, hf, a, b, ha, he⟩
    have hab : DirectSymmetry (realLocus P) a b :=
      ⟨ha, fun z => by rw [← he]; exact hf z⟩
    refine ⟨⟨(a, b), hab⟩, ?_⟩
    apply Subtype.ext
    apply IsometryEquiv.ext
    exact fun z => (he z).symm
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable def directIsometryEquiv (P : BPoly) :
    DirectSymmetries P ≃ directIsometryGroup (realLocus P) :=
  Equiv.ofBijective (directParametersToIsometry P) (directParametersToIsometry_bijective P)
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
theorem solution :
    Nat.card (directIsometryGroup {z : ℂ | (z ^ 4).re = 1}) = 4 ∧
      ¬ ∃ a b α : ℂ, a ≠ 0 ∧ α ≠ star α ∧
        ((fun z : ℂ => a * z + b) '' {z : ℂ | (z ^ 4).re = 1} = extremalCurve 2 α ∨
          (fun z : ℂ => a * star z + b) '' {z : ℂ | (z ^ 4).re = 1} = extremalCurve 2 α) := by
  refine ⟨?_, ?_⟩
  · rw [← realLocus_fermat_four, ← Nat.card_congr (directIsometryEquiv (fermatPolynomial 4))]
    exact fermat_direct_card (by norm_num)
  · rintro ⟨a, b, α, ha, hα, hS | hS⟩
    · exact quartic_not_similar_family hα ha hS
    · exact quartic_not_oppositeSimilar_family hα ha hS
end

#print axioms solution
