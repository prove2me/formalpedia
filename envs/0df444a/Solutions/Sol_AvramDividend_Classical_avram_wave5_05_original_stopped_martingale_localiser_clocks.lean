-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_original_stopped_martingale_localiser_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:39:39.257278+00:00
-- url     : https://prove2.me/submissions/31e1f2fc-e531-46d0-8f10-6b6c366592a5

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The paper's stochastic martingale localizers stop at genuine ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ n, IsStoppingTime 𝓕.rightCont (S n))
    (hSmono : ∀ ω, Monotone (fun n => S n ω))
    (hSsup : ∀ ω, (⨆ n, S n ω) = ⊤) :
    (∀ n : ℕ, IsStoppingTime 𝓕.rightCont
      (fun ω => min (ruinTime X x D ω) (S n ω))) ∧
    (∀ n : ℕ, Measurable
      (fun ω => min (ruinTime X x D ω) (S n ω))) ∧
    (∀ ω, Monotone (fun n => min (ruinTime X x D ω) (S n ω))) ∧
    (∀ ω, (⨆ n, min (ruinTime X x D ω) (S n ω)) =
      ruinTime X x D ω) := by
  constructor
  · intro n
    exact (ruinTime_stopping_rightCont_filtration X x D hD).min (hSstop n)
  constructor
  · intro n
    exact ((ruinTime_stopping_rightCont_filtration X x D hD).min (hSstop n)).measurable'
  constructor
  · intro ω i j hij
    exact min_le_min_left _ (hSmono ω hij)
  · intro ω
    calc
      (⨆ n, min (ruinTime X x D ω) (S n ω)) =
          min (ruinTime X x D ω) (⨆ n, S n ω) := by
        rw [inf_iSup_eq]
      _ = ruinTime X x D ω := by simp [hSsup ω]
