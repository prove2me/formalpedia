-- Prove2me | solution 1 for AvramDividend.Classical.chat04_past_history_future_step_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T22:48:38.220521+00:00
-- url     : https://prove2.me/submissions/3c06ab15-b856-40c8-9c7e-b8d3687c9c94

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_past_statistic_future_increment_product_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
History-valued Markov/Tonelli formula for ANY nonnegative measurable
future-step payoff. This is the general stochastic induction step for
arbitrarily long finite monitoring grids and path-dependent killing.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (H : Ω → E) (hH : Measurable[𝓕 s] H)
    (f : E × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (H ω, X.X t ω - X.X s ω) ∂P) =
      ∫⁻ z, ∫⁻ b, f (z, b)
        ∂(Measure.map (X.X (t - s)) P)
        ∂(Measure.map H P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let m : Ω → E × ℝ :=
    fun ω => (H ω, X.X t ω - X.X s ω)
  have hHm : Measurable H :=
    hH.mono (𝓕.le s) le_rfl
  have hXs : Measurable (X.X s) :=
    (X.adapted s).mono (𝓕.le s) le_rfl
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hm : Measurable m := by
    dsimp [m]
    exact hHm.prodMk (hXt.sub hXs)
  have hProduct :
      Measure.map m P =
        (Measure.map H P).prod
          (Measure.map (X.X (t - s)) P) := by
    simpa only [m] using
      AvramDividend.Classical.chat04_past_statistic_future_increment_product_law
        X s t hst H hH
  calc
    (∫⁻ ω, f (H ω, X.X t ω - X.X s ω) ∂P) =
      ∫⁻ ω, f (m ω) ∂P := by rfl
    _ = ∫⁻ z, f z ∂(Measure.map m P) :=
      (lintegral_map hf hm).symm
    _ = ∫⁻ z, f z ∂
        ((Measure.map H P).prod
          (Measure.map (X.X (t - s)) P)) := by
      rw [hProduct]
    _ = ∫⁻ z, ∫⁻ b, f (z, b)
          ∂(Measure.map (X.X (t - s)) P)
          ∂(Measure.map H P) :=
      lintegral_prod f hf.aemeasurable
