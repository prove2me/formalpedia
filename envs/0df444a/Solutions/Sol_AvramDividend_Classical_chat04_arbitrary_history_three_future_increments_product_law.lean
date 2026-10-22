-- Prove2me | solution 1 for AvramDividend.Classical.chat04_arbitrary_history_three_future_increments_product_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:17:38.59635+00:00
-- url     : https://prove2.me/submissions/8715e22b-c297-456d-bab4-9e44886fb9ad

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_past_statistic_future_increment_product_law
import Theorems.Thm_AvramDividend_Classical_chat04_arbitrary_history_two_future_increments_product_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Fourfold joint product law for arbitrary measurable past history and three
successive future Lévy increments. The proof reuses the accepted two-step
law with an augmented F_t history, then substitutes the independently
verified law of that augmented history.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v)
    (H : Ω → E) (hH : Measurable[𝓕 s] H) :
    Measure.map
      (fun ω => (((H ω, X.X t ω - X.X s ω),
        X.X u ω - X.X t ω), X.X v ω - X.X u ω)) P =
      (((Measure.map H P).prod
        (Measure.map (X.X (t - s)) P)).prod
        (Measure.map (X.X (u - t)) P)).prod
        (Measure.map (X.X (v - u)) P) := by
  let H' : Ω → E × ℝ :=
    fun ω => (H ω, X.X t ω - X.X s ω)
  have hHt : Measurable[𝓕 t] H :=
    hH.mono (𝓕.mono hst) le_rfl
  have hXs_t : Measurable[𝓕 t] (X.X s) :=
    (X.adapted s).mono (𝓕.mono hst) le_rfl
  have hXt_t : Measurable[𝓕 t] (X.X t) := X.adapted t
  have hHistory : Measurable[𝓕 t] H' := by
    dsimp [H']
    exact hHt.prodMk (hXt_t.sub hXs_t)
  have hFirstLaw :
      Measure.map H' P =
        (Measure.map H P).prod
          (Measure.map (X.X (t - s)) P) := by
    simpa only [H'] using
      AvramDividend.Classical.chat04_past_statistic_future_increment_product_law
        X s t hst H hH
  have hTwoMore :
      Measure.map
        (fun ω => ((H' ω, X.X u ω - X.X t ω),
          X.X v ω - X.X u ω)) P =
        ((Measure.map H' P).prod
          (Measure.map (X.X (u - t)) P)).prod
          (Measure.map (X.X (v - u)) P) := by
    exact
      AvramDividend.Classical.chat04_arbitrary_history_two_future_increments_product_law
        X t u v htu huv H' hHistory
  simpa only [H', hFirstLaw] using hTwoMore
