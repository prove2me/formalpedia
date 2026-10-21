-- Prove2me | solution 1 for AvramDividend.Classical.chat04_three_step_grid_tonelli_markov_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:56:52.018206+00:00
-- url     : https://prove2.me/submissions/7635717a-8703-4c62-a709-2ea9a9095125

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_three_consecutive_increment_product_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Two-step Markov-Tonelli identity for *every* Borel nonnegative payoff of
the observed reserve and two consecutive future increments. This permits
grid-survival indicators as payoff kernels, without any moments.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (f : (ℝ × ℝ) × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f ((X.X s ω, X.X t ω - X.X s ω),
        X.X u ω - X.X t ω) ∂P) =
      ∫⁻ a, ∫⁻ b, ∫⁻ c, f ((a, b), c)
        ∂(Measure.map (X.X (u - t)) P)
        ∂(Measure.map (X.X (t - s)) P)
        ∂(Measure.map (X.X s) P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let m : Ω → (ℝ × ℝ) × ℝ :=
    fun ω => ((X.X s ω, X.X t ω - X.X s ω),
      X.X u ω - X.X t ω)
  have hXs : Measurable (X.X s) :=
    (X.adapted s).mono (𝓕.le s) le_rfl
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hXu : Measurable (X.X u) :=
    (X.adapted u).mono (𝓕.le u) le_rfl
  have hm : Measurable m := by
    dsimp [m]
    exact (hXs.prodMk (hXt.sub hXs)).prodMk (hXu.sub hXt)
  have hProduct :
      Measure.map m P =
        ((Measure.map (X.X s) P).prod
          (Measure.map (X.X (t - s)) P)).prod
            (Measure.map (X.X (u - t)) P) := by
    simpa only [m] using
      AvramDividend.Classical.chat04_levy_three_consecutive_increment_product_law
        X s t u hst htu
  have hInnerMeas :
      Measurable
        (fun p : ℝ × ℝ =>
          ∫⁻ c, f (p, c) ∂(Measure.map (X.X (u - t)) P)) := by
    exact Measurable.lintegral_prod_right hf
  calc
    (∫⁻ ω, f ((X.X s ω, X.X t ω - X.X s ω),
          X.X u ω - X.X t ω) ∂P) =
      ∫⁻ ω, f (m ω) ∂P := by rfl
    _ = ∫⁻ z, f z ∂(Measure.map m P) :=
      (lintegral_map hf hm).symm
    _ = ∫⁻ z, f z ∂
        (((Measure.map (X.X s) P).prod
          (Measure.map (X.X (t - s)) P)).prod
            (Measure.map (X.X (u - t)) P)) := by
      rw [hProduct]
    _ = ∫⁻ p, ∫⁻ c, f (p,c)
          ∂(Measure.map (X.X (u - t)) P)
          ∂((Measure.map (X.X s) P).prod
            (Measure.map (X.X (t - s)) P)) :=
      lintegral_prod f hf.aemeasurable
    _ = ∫⁻ a, ∫⁻ b, ∫⁻ c, f ((a,b),c)
          ∂(Measure.map (X.X (u - t)) P)
          ∂(Measure.map (X.X (t - s)) P)
          ∂(Measure.map (X.X s) P) :=
      lintegral_prod
        (fun p : ℝ × ℝ =>
          ∫⁻ c, f (p,c) ∂(Measure.map (X.X (u - t)) P))
        hInnerMeas.aemeasurable
