-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_phys17_original_discounted_reserve_cell_reward_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T18:58:11.852747+00:00
-- url     : https://prove2.me/submissions/909550c9-77c9-4b74-bbd2-11c46af0ec06

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_phys17_original_postright_reserve_source_increment_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0),
      let U : ℝ≥0 → ℝ := fun v => x + X.X v ω - rightLimit D v ω
      let J : ℝ≥0 → ℝ := fun r =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ r then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      Real.exp (-(q * (t : ℝ))) * w (U t) -
        Real.exp (-(q * (s : ℝ))) * w (U s) =
      Real.exp (-(q * (t : ℝ))) *
        (w (U s + (((t : ℝ) - (s : ℝ)) * X.drift -
          (J t - J s) - (rightLimit D t ω - rightLimit D s ω))) -
          w (U s)) +
      (Real.exp (-(q * (t : ℝ))) -
        Real.exp (-(q * (s : ℝ)))) * w (U s) := by
  filter_upwards [
    avram_bv_phys17_original_postright_reserve_source_increment_ae X hX hBV x D
  ] with ω hsource
  intro s t
  dsimp only
  have hstep := hsource s t
  have hu :
      x + X.X t ω - rightLimit D t ω =
      (x + X.X s ω - rightLimit D s ω) +
        (((t : ℝ) - (s : ℝ)) * X.drift -
          ((∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
            else 0) -
           (∑' v : ℝ≥0, if 0 < v ∧ v ≤ s then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
            else 0)) -
          (rightLimit D t ω - rightLimit D s ω)) := by
    linarith only [hstep]
  rw [hu]
  ring
