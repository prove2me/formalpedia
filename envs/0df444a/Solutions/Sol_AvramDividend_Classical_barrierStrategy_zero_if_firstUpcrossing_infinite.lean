-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_zero_if_firstUpcrossing_infinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:45:55.41928+00:00
-- url     : https://prove2.me/submissions/6cf9b61b-251f-4530-875d-bed48c935241

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_before_upcrossing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Infinite first strict upcrossing entails no barrier payments
    at any finite time, on that very sample path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (ω : Ω)
    (hnever : (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω),
      (s : ℝ≥0∞)) = ⊤) :
    ∀ t : ℝ≥0, barrierStrategy X x a t ω = 0 := by
  intro t
  apply barrierStrategy_zero_before_upcrossing X x a t ω
  intro s hs
  by_contra hnot
  have hcross : a - x < X.X s ω := lt_of_not_ge hnot
  have hle :
      (⨅ (r : ℝ≥0) (_ : a - x < X.X r ω),
        (r : ℝ≥0∞)) ≤ (s : ℝ≥0∞) :=
    iInf_le_of_le s (iInf_le (fun _ : a - x < X.X s ω => (s : ℝ≥0∞)) hcross)
  rw [hnever] at hle
  have htop : (s : ℝ≥0∞) = ⊤ := top_le_iff.mp hle
  exact (ENNReal.coe_ne_top : (s : ℝ≥0∞) ≠ ⊤) htop