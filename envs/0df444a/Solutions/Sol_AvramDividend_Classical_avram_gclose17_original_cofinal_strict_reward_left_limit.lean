-- Prove2me | solution 1 for AvramDividend.Classical.avram_gclose17_original_cofinal_strict_reward_left_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:09:59.048519+00:00
-- url     : https://prove2.me/submissions/a15e3315-f73d-48ac-92cc-acc813a7702e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gfinite15_original_discounted_terminal_left_limit
import Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_strict_cash_real_monotone_cofinal_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The exact original discounted prepayment terminal and strict Stieltjes
cash converge jointly along cofinal left physical clocks, including ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (q : ℝ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) ≤ ruinTime X x D ω →
      ∀ (u : ℕ → ℝ≥0), Monotone u →
        (∀ n, u n < t) → Tendsto u atTop (𝓝[<] t) →
        Tendsto (fun n =>
          Real.exp (-(q * (u n : ℝ))) *
              w (x + X.X (u n) ω - rightLimit D (u n) ω) +
            (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (u n : ℝ),
              ENNReal.ofReal (Real.exp (-(q * s)))
              ∂(dividendMeasure D ω)).toReal)
          atTop
          (𝓝 (Real.exp (-(q * (t : ℝ))) *
              w (riskProcess X x D t ω) +
            (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (t : ℝ),
              ENNReal.ofReal (Real.exp (-(q * s)))
              ∂(dividendMeasure D ω)).toReal)) := by
  filter_upwards [
    avram_gfinite15_original_discounted_terminal_left_limit
      X hν x C D hD w hw q] with ω hω
  intro t ht hruin u hmono hbelow hu
  have hTerm := (hω t ht hruin).comp hu
  have hNear : Tendsto u atTop (𝓝 t) :=
    hu.mono_right nhdsWithin_le_nhds
  have hReal : Tendsto (fun n => (u n : ℝ)) atTop (𝓝 (t : ℝ)) :=
    (NNReal.continuous_coe.tendsto t).comp hNear
  have hT : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hm : Monotone (fun n => (u n : ℝ)) := by
    intro i j hij
    exact_mod_cast hmono hij
  have hb (n : ℕ) : (u n : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast le_of_lt (hbelow n)
  have hc (s : ℝ) (hs : s < (t : ℝ)) :
      ∃ n, s < (u n : ℝ) := by
    have hevent : ∀ᶠ n in atTop, s < (u n : ℝ) :=
      hReal.eventually (Ioi_mem_nhds hs)
    exact hevent.exists
  have hCash :=
    avram_gclose17_original_strict_cash_real_monotone_cofinal_clock
      X x C D hD ω q (le_of_lt hq) (t : ℝ) hT
      (fun n => (u n : ℝ)) hm hb hc
  exact hTerm.add hCash
