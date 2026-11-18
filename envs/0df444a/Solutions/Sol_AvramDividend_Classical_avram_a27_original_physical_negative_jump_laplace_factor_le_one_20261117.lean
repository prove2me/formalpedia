-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_negative_jump_laplace_factor_le_one_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:03:57.3632+00:00
-- url     : https://prove2.me/submissions/0388b865-981f-4c27-907b-977a8e750f3a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a88_original_physical_negative_jump_exponential_finite_product_20261114
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The actual negative-mark Laplace factor is strictly positive and at most one. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) (J : Ω → ℝ)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0) :
    ∀ᵐ ω ∂P,
      0 < Real.exp (θ * J ω) ∧ Real.exp (θ * J ω) ≤ 1 := by
  classical
  have hProduct :=
    avram_a88_original_physical_negative_jump_exponential_finite_product_20261114
      X hFinite t θ J hJEq
  filter_upwards [hProduct] with ω hP
  rcases hP with ⟨S, hS, hEq⟩
  constructor
  · exact Real.exp_pos _
  · rw [hEq]
    apply Finset.prod_le_one
    · intro u hu
      have ht : u ≤ t := ((hS u).mp hu).2.1
      simp only [if_pos ht]
      exact le_of_lt (Real.exp_pos _)
    · intro u hu
      have hpos : 0 < u := ((hS u).mp hu).1
      have ht : u ≤ t := ((hS u).mp hu).2.1
      have hJump :=
        avram_wave4_04a_actual_levy_jumpmark_nonpositive X ω u hpos
      simp only [if_pos ht]
      exact (Real.exp_le_one_iff).2
        (mul_nonpos_of_nonneg_of_nonpos hθ hJump)
