-- Prove2me | solution 1 for AvramDividend.Classical.chat03_grid_upperfirst_lintegral_tendsto_no_finite_ties
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:22:36.339969+00:00
-- url     : https://prove2.me/submissions/69775fb5-9558-438d-ace5-f0b95111107d

import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_payoff_tendsto_without_finite_ties
import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_lintegral_tendsto_of_ae_payoff
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal

/-!
Expected grid-to-continuous first-passage discount convergence
under almost-sure clock convergence, no finite ties and persistent
non-exit of the sampled upper clock on infinite-passage paths.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ) (hq : 0 ≤ q)
    (upGrid downGrid : ℕ → Ω → ℝ≥0∞)
    (up down : Ω → ℝ≥0∞)
    (hu : ∀ n, Measurable (upGrid n))
    (hd : ∀ n, Measurable (downGrid n))
    (hup : ∀ᵐ ω ∂P, Tendsto
      (fun n => upGrid n ω) atTop (𝓝 (up ω)))
    (hdown : ∀ᵐ ω ∂P, Tendsto
      (fun n => downGrid n ω) atTop (𝓝 (down ω)))
    (hfiniteTie : ∀ᵐ ω ∂P,
      up ω = down ω → up ω = ∞)
    (hNoUpGrid : ∀ᵐ ω ∂P,
      up ω = ∞ → ∀ n : ℕ, upGrid n ω = ∞) :
    Tendsto
      (fun n => ∫⁻ ω,
        if upGrid n ω < downGrid n ω then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (upGrid n ω))))
        else 0 ∂P)
      atTop
      (𝓝 (∫⁻ ω,
        if up ω < down ω then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (up ω))))
        else 0 ∂P)) := by
  apply chat03_grid_upperfirst_lintegral_tendsto_of_ae_payoff
    P q hq upGrid downGrid up down hu hd
  filter_upwards [hup, hdown, hfiniteTie, hNoUpGrid]
    with ω huω hdω htie hno
  exact chat03_grid_upperfirst_payoff_tendsto_without_finite_ties
    q (up ω) (down ω)
    (fun n => upGrid n ω) (fun n => downGrid n ω)
    huω hdω htie hno
