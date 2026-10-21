-- Prove2me | solution 1 for AvramDividend.Classical.chat04_history_two_step_markov_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T22:57:46.243839+00:00
-- url     : https://prove2.me/submissions/549bebc2-b51e-4ea0-8093-feb089b627bc

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_arbitrary_history_two_future_increments_product_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Threefold Markov/Tonelli formula for an arbitrary F_s-measurable history
and two future Lévy increments. Every nonnegative Borel cylinder payoff is
allowed, including discrete first-exit and path-survival indicators.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (H : Ω → E) (hH : Measurable[𝓕 s] H)
    (f : (E × ℝ) × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f ((H ω, X.X t ω - X.X s ω),
        X.X u ω - X.X t ω) ∂P) =
      ∫⁻ z, ∫⁻ a, ∫⁻ b, f ((z, a), b)
        ∂(Measure.map (X.X (u - t)) P)
        ∂(Measure.map (X.X (t - s)) P)
        ∂(Measure.map H P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let m : Ω → (E × ℝ) × ℝ :=
    fun ω => ((H ω, X.X t ω - X.X s ω),
      X.X u ω - X.X t ω)
  have hHm : Measurable H := hH.mono (𝓕.le s) le_rfl
  have hXs : Measurable (X.X s) :=
    (X.adapted s).mono (𝓕.le s) le_rfl
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hXu : Measurable (X.X u) :=
    (X.adapted u).mono (𝓕.le u) le_rfl
  have hm : Measurable m := by
    dsimp [m]
    exact (hHm.prodMk (hXt.sub hXs)).prodMk (hXu.sub hXt)
  have hProduct :
      Measure.map m P =
        ((Measure.map H P).prod
          (Measure.map (X.X (t - s)) P)).prod
            (Measure.map (X.X (u - t)) P) := by
    simpa only [m] using
      AvramDividend.Classical.chat04_arbitrary_history_two_future_increments_product_law
        X s t u hst htu H hH
  have hInnerMeas :
      Measurable
        (fun p : E × ℝ =>
          ∫⁻ b, f (p, b) ∂(Measure.map (X.X (u - t)) P)) :=
    Measurable.lintegral_prod_right hf
  calc
    (∫⁻ ω, f ((H ω, X.X t ω - X.X s ω),
          X.X u ω - X.X t ω) ∂P) =
      ∫⁻ ω, f (m ω) ∂P := by rfl
    _ = ∫⁻ v, f v ∂(Measure.map m P) :=
      (lintegral_map hf hm).symm
    _ = ∫⁻ v, f v ∂
        (((Measure.map H P).prod
          (Measure.map (X.X (t - s)) P)).prod
            (Measure.map (X.X (u - t)) P)) := by
      rw [hProduct]
    _ = ∫⁻ p, ∫⁻ b, f (p,b)
          ∂(Measure.map (X.X (u - t)) P)
          ∂((Measure.map H P).prod
            (Measure.map (X.X (t - s)) P)) :=
      lintegral_prod f hf.aemeasurable
    _ = ∫⁻ z, ∫⁻ a, ∫⁻ b, f ((z,a),b)
          ∂(Measure.map (X.X (u - t)) P)
          ∂(Measure.map (X.X (t - s)) P)
          ∂(Measure.map H P) :=
      lintegral_prod
        (fun p : E × ℝ =>
          ∫⁻ b, f (p,b) ∂(Measure.map (X.X (u - t)) P))
        hInnerMeas.aemeasurable
