-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn13_original_loss_le_strict_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:30:53.31696+00:00
-- url     : https://prove2.me/submissions/73c66092-58b0-4920-9db1-c606adcb9b64

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Each actual marked loss is below one, giving a finite-cardinality bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
      (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    ∀ ω : Ω, L ω ≤ ((S ω).card : ℝ) := by
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let S : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
    (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  change ∀ ω : Ω, L ω ≤ ((S ω).card : ℝ)
  intro ω
  dsimp [L]
  calc
    (∑ u ∈ S ω,
      (1 - Real.exp (X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u))) ≤
        ∑ u ∈ S ω, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro u hu
          have hexp : 0 ≤ Real.exp (X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) :=
            (Real.exp_pos _).le
          linarith
    _ = ((S ω).card : ℝ) := by simp
