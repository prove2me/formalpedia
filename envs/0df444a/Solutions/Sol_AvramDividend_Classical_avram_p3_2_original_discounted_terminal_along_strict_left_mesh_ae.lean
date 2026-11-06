-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_discounted_terminal_along_strict_left_mesh_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:10:16.08317+00:00
-- url     : https://prove2.me/submissions/f9f9d611-fd79-47d5-9170-d4dca6e159bf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_discounted_survivor_pre_rightpayment_terminal_left_tendsto_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Every original strictly left-approaching time mesh inherits the almost
sure discounted pre-rightpayment w terminal limit on strict survival. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (q : ℝ) (t : ℝ≥0) (ht : 0 < t)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n < t)
    (huLimit : Tendsto u atTop (𝓝 t)) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ruinTime X x D ω →
      Tendsto (fun n : ℕ =>
        Real.exp (-(q * (u n : ℝ))) *
          w (x + X.X (u n) ω - rightLimit D (u n) ω))
        atTop
        (𝓝 (Real.exp (-(q * (t : ℝ))) *
          w (riskProcess X x D t ω))) := by
  have huWithin : Tendsto u atTop (𝓝[<] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨huLimit,
      Filter.Eventually.of_forall (fun n => hu n)⟩
  filter_upwards [avram_p3_2_original_discounted_survivor_pre_rightpayment_terminal_left_tendsto_ae
    X x C D hD w hw_cont q t ht] with ω hTerminal
  intro hSurvive
  exact (hTerminal hSurvive).comp huWithin
