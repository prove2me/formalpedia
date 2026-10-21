-- Prove2me | solution 1 for AvramDividend.Classical.grid_exit_fatou_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:00:17.123771+00:00
-- url     : https://prove2.me/submissions/88176fa5-f604-48b9-a116-152450359310

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Order.LiminfLimsup
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal

/-- Fatou transports a uniform grid-payoff bound to a dominated continuous-passage limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Ω → ENNReal) (f : ℕ → Ω → ENNReal)
    (hMeas : ∀ n : ℕ, Measurable (f n))
    (hlimit : ∀ ω : Ω, F ω ≤ liminf (fun n => f n ω) atTop)
    (B : ENNReal)
    (hgrid : ∀ n : ℕ, (∫⁻ ω, f n ω ∂P) ≤ B) :
    (∫⁻ ω, F ω ∂P) ≤ B := by
  have hFatou :
      (∫⁻ ω, liminf (fun n => f n ω) atTop ∂P) ≤
        liminf (fun n => ∫⁻ ω, f n ω ∂P) atTop :=
    lintegral_liminf_le hMeas
  have hliminf :
      liminf (fun n => ∫⁻ ω, f n ω ∂P) atTop ≤ B := by
    refine Filter.liminf_le_of_le (hf := by isBoundedDefault) ?_
    intro b hb
    have he : ∀ᶠ n : ℕ in atTop, b ≤ B :=
      hb.mono (fun n hn => le_trans hn (hgrid n))
    rcases he.exists with ⟨n, hn⟩
    exact hn
  exact (lintegral_mono hlimit).trans (hFatou.trans hliminf)
