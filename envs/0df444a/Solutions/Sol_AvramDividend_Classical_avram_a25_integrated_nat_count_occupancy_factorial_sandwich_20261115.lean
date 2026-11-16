-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_integrated_nat_count_occupancy_factorial_sandwich_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:01:42.361397+00:00
-- url     : https://prove2.me/submissions/19dfb7ee-e359-494b-a299-03520aae679a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a25_nat_count_occupancy_factorial_sandwich_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
noncomputable section

/-- Expected factorial count moments bound probability of a nonempty count. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (hFirst : Integrable (fun ω => (K ω : ℝ)) P)
    (hSecond : Integrable
      (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P) :
    (∫ ω, (K ω : ℝ) ∂P) -
        (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) / 2 ≤
      (P {ω : Ω | K ω ≠ 0}).toReal ∧
    (P {ω : Ω | K ω ≠ 0}).toReal ≤
      (∫ ω, (K ω : ℝ) ∂P) := by
  let s : Set Ω := {ω | K ω ≠ 0}
  have hs : MeasurableSet s := by
    change MeasurableSet (K ⁻¹' ({(0 : ℕ)}ᶜ))
    exact hK ((measurableSet_singleton (0 : ℕ)).compl)
  have hI : Integrable (s.indicator (fun _ : Ω => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hs
  have hL : Integrable
      (fun ω => (K ω : ℝ) -
        ((K ω : ℝ) * ((K ω : ℝ) - 1)) / 2) P :=
    hFirst.sub (hSecond.div_const 2)
  have hPoint (ω : Ω) :
      (K ω : ℝ) - ((K ω : ℝ) * ((K ω : ℝ) - 1)) / 2 ≤
          s.indicator (fun _ => (1 : ℝ)) ω ∧
        s.indicator (fun _ => (1 : ℝ)) ω ≤ (K ω : ℝ) := by
    have h := avram_a25_nat_count_occupancy_factorial_sandwich_20261115 (K ω)
    by_cases hk : K ω = 0
    · simpa [s, hk] using h
    · simpa [s, hk] using h
  have hLower := integral_mono_ae hL hI
    (Filter.Eventually.of_forall (fun ω => (hPoint ω).1))
  have hUpper := integral_mono_ae hI hFirst
    (Filter.Eventually.of_forall (fun ω => (hPoint ω).2))
  have hEval : (∫ ω, s.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P) =
      (P s).toReal := by
    change (∫ ω, s.indicator (1 : Ω → ℝ) ω ∂P) = P.real s
    exact integral_indicator_one (μ := P) hs
  have hLinear :
      (∫ ω, (K ω : ℝ) -
        ((K ω : ℝ) * ((K ω : ℝ) - 1)) / 2 ∂P) =
      (∫ ω, (K ω : ℝ) ∂P) -
        (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) / 2 := by
    rw [integral_sub hFirst (hSecond.div_const 2), integral_div]
  constructor
  · simpa only [hLinear, hEval, s] using hLower
  · simpa only [hEval, s] using hUpper
