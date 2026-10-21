-- Prove2me | solution 1 for AvramDividend.Classical.chat04_three_time_state_path_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T07:16:43.105049+00:00
-- url     : https://prove2.me/submissions/e66debdb-9d48-426d-bde1-bf14240d5ace

import Mathlib.Tactic.FunProp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_three_step_grid_tonelli_markov_law
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Full three-time state-path Markov-Tonelli formula. Any Borel payoff of
the actual states (X_s,X_t,X_u), including discrete ruin indicators,
is integrated against independent successive increments.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (f : (ℝ × ℝ) × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f ((X.X s ω, X.X t ω), X.X u ω) ∂P) =
      ∫⁻ a, ∫⁻ b, ∫⁻ c, f ((a, a + b), a + b + c)
        ∂(Measure.map (X.X (u - t)) P)
        ∂(Measure.map (X.X (t - s)) P)
        ∂(Measure.map (X.X s) P) := by
  let k : ((ℝ × ℝ) × ℝ) → ((ℝ × ℝ) × ℝ) :=
    fun z => ((z.1.1, z.1.1 + z.1.2),
      z.1.1 + z.1.2 + z.2)
  have hk : Measurable k := by
    dsimp [k]
    fun_prop
  have hfk : Measurable (f ∘ k) := hf.comp hk
  have hrewrite (ω : Ω) :
      f ((X.X s ω, X.X t ω), X.X u ω) =
        (f ∘ k)
          ((X.X s ω, X.X t ω - X.X s ω),
            X.X u ω - X.X t ω) := by
    have h1 :
        X.X s ω + (X.X t ω - X.X s ω) = X.X t ω := by ring
    have h2 :
        X.X s ω + (X.X t ω - X.X s ω) +
          (X.X u ω - X.X t ω) = X.X u ω := by ring
    have h3 : X.X t ω + (X.X u ω - X.X t ω) = X.X u ω := by
      ring
    simp only [Function.comp_def, k, h1, h3]
  calc
    (∫⁻ ω, f ((X.X s ω, X.X t ω), X.X u ω) ∂P) =
        ∫⁻ ω,
          (f ∘ k)
            ((X.X s ω, X.X t ω - X.X s ω),
              X.X u ω - X.X t ω) ∂P :=
        lintegral_congr hrewrite
    _ = ∫⁻ a, ∫⁻ b, ∫⁻ c, f ((a, a + b), a + b + c)
          ∂(Measure.map (X.X (u - t)) P)
          ∂(Measure.map (X.X (t - s)) P)
          ∂(Measure.map (X.X s) P) := by
        simpa only [Function.comp_def, k] using
          (AvramDividend.Classical.chat04_three_step_grid_tonelli_markov_law
            X s t u hst htu (f ∘ k) hfk)
