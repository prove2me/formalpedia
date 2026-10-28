-- Prove2me | solution 1 for D1Bound5.exists_imaginary_quadratic_ring_equiv
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T22:57:39.871959+00:00
-- url     : https://prove2.me/submissions/beee3f5b-6dc5-4bd8-8447-734bea338caa

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
import Theorems.Thm_D1Bound5_QuadInt_complex_generator_parameters
import Theorems.Thm_D1Bound5_exists_normalized_quadratic_ring_equiv
import Theorems.Thm_D1Bound5_full_ring_generator_nonreal

section
namespace D1Bound5.QuadInt

open scoped QuadraticAlgebra

variable {tau nu : ℤ}





/-- Positivity of the coordinate discriminant follows from any nonreal
complex embedding, rather than being assumed as an extra field hypothesis. -/
theorem discriminant_pos_of_complex_embedding (f : QuadInt tau nu →+* ℂ)
    (hi : (f QuadraticAlgebra.omega).im ≠ 0) : 0 < discriminant tau nu := by
  have h := (complex_generator_parameters f hi).2.2
  have hs := sq_pos_of_ne_zero hi
  have hd : (0 : ℝ) < (discriminant tau nu : ℝ) := by linarith
  exact_mod_cast hd





end D1Bound5.QuadInt
end

section
open scoped NumberField ComplexConjugate
open Module

namespace D1Bound5

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]



/-- Every imaginary quadratic field has full integer-ring coordinates of
trace zero or one and positive discriminant. There is no suborder hypothesis. -/
theorem _root_.solution (hK : finrank ℚ K = 2) :
    ∃ tau nu : ℤ, (tau = 0 ∨ tau = 1) ∧ 0 < QuadInt.discriminant tau nu ∧
      Nonempty (QuadInt tau nu ≃+* 𝓞 K) := by
  obtain ⟨tau, nu, ht, ⟨e⟩⟩ := exists_normalized_quadratic_ring_equiv hK
  let φ : K →+* ℂ := Classical.choice inferInstance
  refine ⟨tau, nu, ht, ?_, ⟨e⟩⟩
  exact QuadInt.discriminant_pos_of_complex_embedding _ (full_ring_generator_nonreal e φ)







end D1Bound5
end
