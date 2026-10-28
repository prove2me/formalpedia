-- Prove2me | solution 1 for D1Bound5.full_ring_generator_nonreal
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:21:57.671744+00:00
-- url     : https://prove2.me/submissions/ccef98cb-fc51-4ab9-b105-db89f83b9821

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_QuadInt_complex_image

section
open scoped NumberField ComplexConjugate
open Module

namespace D1Bound5

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]

/-- A generator of the full number ring cannot have a real image in a
complex embedding of a totally complex field. Fraction representations
extend reality from the integer ring to the whole field. -/
theorem _root_.solution {tau nu : ℤ}
    (e : QuadInt tau nu ≃+* 𝓞 K) (φ : K →+* ℂ) :
    (((φ.comp (algebraMap (𝓞 K) K)).comp e.toRingHom) QuadraticAlgebra.omega).im ≠ 0 := by
  let f : QuadInt tau nu →+* ℂ := (φ.comp (algebraMap (𝓞 K) K)).comp e.toRingHom
  intro hi
  change (f QuadraticAlgebra.omega).im = 0 at hi
  have hreal (x : 𝓞 K) : conj (φ (x : K)) = φ (x : K) := by
    obtain ⟨z, rfl⟩ := e.surjective x
    apply Complex.conj_eq_iff_im.mpr
    change (f z).im = 0
    rw [QuadInt.complex_image f z]
    simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im,
      hi, mul_zero, zero_mul, add_zero]
  apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal φ
  apply NumberField.ComplexEmbedding.isReal_iff.mpr
  ext x
  change conj (φ x) = φ x
  obtain ⟨a, b, _, hx⟩ := IsFractionRing.div_surjective (𝓞 K) x
  rw [← hx]
  simp only [map_div₀, hreal]









end D1Bound5
end
