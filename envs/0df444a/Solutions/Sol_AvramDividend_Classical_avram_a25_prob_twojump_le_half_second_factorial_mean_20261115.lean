-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_prob_twojump_le_half_second_factorial_mean_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:04:13.221128+00:00
-- url     : https://prove2.me/submissions/2d90c25d-3184-48d2-9d61-32e780bfe9b5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a25_nat_twojump_indicator_le_half_factorial_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
noncomputable section

/-- Two or more jumps are controlled by the second factorial count moment. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (hSecond : Integrable
      (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P) :
    (P {ω | 2 ≤ K ω}).toReal ≤
      (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) / 2 := by
  let s : Set Ω := {ω | 2 ≤ K ω}
  have hs : MeasurableSet s := hK measurableSet_Ici
  have hInd : Integrable (s.indicator (fun _ : Ω => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hs
  have hDiv := hSecond.div_const 2
  have hPoint (ω : Ω) :
      s.indicator (fun _ : Ω => (1 : ℝ)) ω ≤
        ((K ω : ℝ) * ((K ω : ℝ) - 1)) / 2 := by
    have h := avram_a25_nat_twojump_indicator_le_half_factorial_20261115 (K ω)
    by_cases hk : 2 ≤ K ω
    · simpa [s, hk] using h
    · simpa [s, hk] using h
  have hBound := integral_mono_ae hInd hDiv
    (Filter.Eventually.of_forall hPoint)
  have hEval :
      (∫ ω, s.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P) =
      (P s).toReal := by
    change (∫ ω, s.indicator (1 : Ω → ℝ) ω ∂P) = P.real s
    exact integral_indicator_one (μ := P) hs
  rw [hEval, integral_div] at hBound
  exact hBound
