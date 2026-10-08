-- Prove2me | solution 1 for CurveSymmetry.quartic_not_oppositeSimilar_family
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:17:39.234169+00:00
-- url     : https://prove2.me/submissions/a35aac5b-4b9d-4012-b6cd-1765abfa4883

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
import Theorems.Thm_CurveSymmetry_quartic_not_similar_family
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
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
/-- The quartic `Re(z⁴) = 1` is symmetric under conjugation. -/
lemma image_star_quartic (a b : ℂ) :
    (fun z : ℂ => a * star z + b) '' {z : ℂ | (z ^ 4).re = 1} =
      (fun z : ℂ => a * z + b) '' {z : ℂ | (z ^ 4).re = 1} := by
  have hstar : star '' {z : ℂ | (z ^ 4).re = 1} = {z : ℂ | (z ^ 4).re = 1} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [← map_pow, Complex.conj_re] using hz
    · intro hw
      exact ⟨star w, by simpa [← map_pow, Complex.conj_re] using hw, star_star w⟩
  calc (fun z : ℂ => a * star z + b) '' {z : ℂ | (z ^ 4).re = 1}
      = (fun z : ℂ => a * z + b) '' (star '' {z : ℂ | (z ^ 4).re = 1}) := by
        rw [Set.image_image]
    _ = (fun z : ℂ => a * z + b) '' {z : ℂ | (z ^ 4).re = 1} := by rw [hstar]
end Quartic
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
local notation "K₄" => KummerField 4 fermatQuartic
theorem solution {α : ℂ} (hα : α ≠ star α) {a b : ℂ} (ha : a ≠ 0) :
    (fun z : ℂ => a * star z + b) '' {z : ℂ | (z ^ 4).re = 1} ≠ extremalCurve 2 α := by
  rw [image_star_quartic]
  exact quartic_not_similar_family hα ha
end

#print axioms solution
