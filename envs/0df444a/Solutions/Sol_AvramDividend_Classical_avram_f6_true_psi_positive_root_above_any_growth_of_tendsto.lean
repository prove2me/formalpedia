-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_true_psi_positive_root_above_any_growth_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:29:06.661922+00:00
-- url     : https://prove2.me/submissions/9eb4e49b-7e79-4c95-8f67-bd73e628abe6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_eventual_psi_above_q_of_tendsto_atTop
set_option autoImplicit false
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hψ : Tendsto X.ψ atTop atTop)
    (θ : ℝ) :
    ∃ p lam : ℝ,
      0 < p ∧ 0 < lam ∧ θ < lam ∧ X.ψ lam = p := by
  obtain ⟨β0, hβ0, hLarge⟩ :=
    eventual_psi_above_q_of_tendsto_atTop X.ψ 0 hψ
  let lam : ℝ := max β0 θ + 1
  have hβ : β0 ≤ lam := by dsimp [lam]; linarith [le_max_left β0 θ]
  have hθ : θ < lam := by dsimp [lam]; linarith [le_max_right β0 θ]
  have hlam : 0 < lam := by
    dsimp [lam]
    have hmax := le_max_left β0 θ
    linarith
  have hp : 0 < X.ψ lam := hLarge lam hβ
  exact ⟨X.ψ lam, lam, hp, hlam, hθ, rfl⟩
