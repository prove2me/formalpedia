-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_positive_clock_source_and_payment_simultaneous_jump_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:51:02.542638+00:00
-- url     : https://prove2.me/submissions/b4e59905-1075-40f1-9da3-fb2f391415dd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Literal original source and right-dividend simultaneous jump: the full
change plus the payable right-atom is bounded by the source-only value
change. The controlled reserve mark splits exactly as source minus payment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hpre : (t : ℝ≥0∞) < ruinTime X x D ω) :
    (w (x + X.X t ω - rightLimit D t ω) -
      w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) +
      (rightLimit D t ω - D t ω) ≤
        w (x + X.X t ω - D t ω) -
          w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω)) ∧
    ((x + X.X t ω - rightLimit D t ω) -
      (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) =
      (X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) -
        (rightLimit D t ω - D t ω)) := by
  constructor
  · have hDrop := hjump ω t (Or.inr hpre)
    change rightLimit D t ω - D t ω ≤
      w (x + X.X t ω - D t ω) -
      w ((x + X.X t ω - D t ω) -
        (rightLimit D t ω - D t ω)) at hDrop
    have hPost : (x + X.X t ω - D t ω) -
        (rightLimit D t ω - D t ω) =
        x + X.X t ω - rightLimit D t ω := by ring
    rw [hPost] at hDrop
    linarith only [hDrop]
  · ring
