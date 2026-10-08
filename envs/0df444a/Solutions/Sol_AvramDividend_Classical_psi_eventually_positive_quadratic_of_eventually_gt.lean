-- Prove2me | solution 1 for AvramDividend.Classical.psi_eventually_positive_quadratic_of_eventually_gt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T21:03:35.327829+00:00
-- url     : https://prove2.me/submissions/530a2e5d-11da-49d0-9e91-76f46f08ad80

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_quadratic_upper

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q β0 : ℝ)
    (hβ0 : 0 ≤ β0)
    (hgt : ∀ θ : ℝ, β0 ≤ θ → q < X.ψ θ) :
    ∃ β C : ℝ, 0 ≤ β ∧ 0 ≤ C ∧
      ∀ θ : ℝ, β ≤ θ →
        q < X.ψ θ ∧ X.ψ θ - q ≤ C * (1 + θ ^ 2) := by
  let C0 : ℝ :=
    |X.c| + X.σ ^ 2 / 2 +
      ∫ y in Ioo (-1 : ℝ) 0, y ^ 2 ∂X.ν
  let β : ℝ := max β0 1
  let C : ℝ := |C0| + |q|
  have hβ : 0 ≤ β := by
    dsimp [β]
    exact le_trans hβ0 (le_max_left _ _)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨β, C, hβ, hC, ?_⟩
  intro θ hθ
  have hβ0θ : β0 ≤ θ :=
    le_trans (le_max_left β0 1) hθ
  have h1θ : 1 ≤ θ :=
    le_trans (le_max_right β0 1) hθ
  have hpos : q < X.ψ θ := hgt θ hβ0θ
  have hup : X.ψ θ ≤ C0 * θ ^ 2 := by
    simpa [C0] using psi_quadratic_upper X θ h1θ
  have hC0 : C0 ≤ |C0| := le_abs_self C0
  have hq : -q ≤ |q| := neg_le_abs q
  have hsq : 0 ≤ θ ^ 2 := sq_nonneg θ
  have hco : 0 ≤ |C0| := abs_nonneg C0
  have hqo : 0 ≤ |q| := abs_nonneg q
  constructor
  · exact hpos
  · dsimp [C]
    nlinarith
