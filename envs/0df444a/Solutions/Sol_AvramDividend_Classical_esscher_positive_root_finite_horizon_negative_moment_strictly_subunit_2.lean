-- Prove2me | solution 2 for AvramDividend.Classical.esscher_positive_root_finite_horizon_negative_moment_strictly_subunit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:37:46.595406+00:00
-- url     : https://prove2.me/submissions/eb3e8268-0705-468b-ac53-f230b79c102a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_has_negative_left_shift_exponent
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_negative_laplace
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) :
    ∃ ε : ℝ, 0 < ε ∧ ε < φ ∧
      ∀ t : ℝ≥0, 0 < t →
        (∫ ω, Real.exp (-ε * X.X t ω) ∂
          (P.withDensity (fun ω : Ω =>
            ENNReal.ofReal
              (Real.exp (φ * X.X t ω - (t : ℝ) * X.ψ φ))))) < 1 := by
  obtain ⟨ε, hε, hεφ, hbelow⟩ :=
    esscher_positive_root_has_negative_left_shift_exponent
      X q φ hq hφ hroot
  refine ⟨ε, hε, hεφ, ?_⟩
  intro t ht
  rw [chat04_esscher_weighted_finite_horizon_negative_laplace
    X t φ ε (le_of_lt hφ) (le_of_lt hε) (le_of_lt hεφ)]
  apply Real.exp_lt_one_iff.mpr
  have htReal : 0 < (t : ℝ) := by exact_mod_cast ht
  have hneg : X.ψ (φ - ε) - X.ψ φ < 0 := by
    rw [hroot]
    linarith
  exact mul_neg_of_pos_of_neg htReal hneg
