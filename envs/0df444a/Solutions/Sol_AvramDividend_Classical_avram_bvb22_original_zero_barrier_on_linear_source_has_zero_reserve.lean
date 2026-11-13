-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb22_original_zero_barrier_on_linear_source_has_zero_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:26:07.714127+00:00
-- url     : https://prove2.me/submissions/c6eb7c5a-6632-4dbc-a78b-8655ba15fa5c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_runningSup_linear_of_linear_capital_prefix
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (hDrift : 0 ≤ X.drift)
    (hPath : ∀ t : ℝ≥0, t ≤ T →
      X.X t ω = X.drift * (t : ℝ)) :
    ∀ t : ℝ≥0, t ≤ T →
      barrierStrategy X 0 0 t ω = X.drift * (t : ℝ) ∧
      riskProcess X 0 (barrierStrategy X 0 0) t ω = 0  := by
  intro t ht
  have hsup : runningSup X t ω = X.drift * (t : ℝ) :=
    runningSup_linear_of_linear_capital_prefix X ω t hDrift
      (fun u hu => hPath u (hu.trans ht))
  have hb : barrierStrategy X 0 0 t ω = X.drift * (t : ℝ) := by
    rw [barrierStrategy_self_eq_runningSup X 0 ω t]
    exact hsup
  refine ⟨hb, ?_⟩
  simp only [riskProcess, hPath t ht, hb]
  ring
