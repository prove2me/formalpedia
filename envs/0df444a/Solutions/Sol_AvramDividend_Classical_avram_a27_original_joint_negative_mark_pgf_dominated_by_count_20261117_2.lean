-- Prove2me | solution 2 for AvramDividend.Classical.avram_a27_original_joint_negative_mark_pgf_dominated_by_count_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:26:45.088822+00:00
-- url     : https://prove2.me/submissions/50eaeadc-5940-4983-bc81-868567ecbf9e

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a85_original_physical_negative_jump_exponential_integrable_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∀ᵐ ω ∂P, 0 ≤ z ^ (K ω) * Real.exp (θ * J ω) ∧
      z ^ (K ω) * Real.exp (θ * J ω) ≤ z ^ (K ω) := by
  obtain ⟨_, hBound⟩ :=
    avram_a85_original_physical_negative_jump_exponential_integrable_20261114
      X hFinite t θ hθ J hJMeas hJEq
  filter_upwards [hBound] with ω hω
  constructor
  · exact mul_nonneg (pow_nonneg hz _) (le_of_lt hω.1)
  · exact mul_le_of_le_one_right (pow_nonneg hz _) hω.2
