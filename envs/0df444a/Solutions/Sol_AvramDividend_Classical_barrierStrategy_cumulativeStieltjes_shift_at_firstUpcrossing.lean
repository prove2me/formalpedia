-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_cumulativeStieltjes_shift_at_firstUpcrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:26:52.118535+00:00
-- url     : https://prove2.me/submissions/aaa1b341-2d18-4a39-9ca1-ea032cb7b564

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Interval.Set.LinearOrder
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_until_firstUpcrossing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_shifted_runningSup_dividendMeasure_Ioc_unconditional

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Zero pre-passage dividends convert shifted-window equality into
    equality of cumulative Stieltjes payments from the initial time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    ∀ t : ℝ≥0,
      (dividendMeasure (barrierStrategy X x a) ω)
        (Set.Ioc (0 : ℝ) ((u + t : ℝ≥0) : ℝ)) =
      (dividendMeasure
        (fun r _ =>
          sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
        ω) (Set.Ioc (0 : ℝ) (t : ℝ)) := by
  intro t
  let μ := dividendMeasure (barrierStrategy X x a) ω
  have hu0 : (0 : ℝ) ≤ (u : ℝ) := u.property
  have hut : (u : ℝ) ≤ ((u + t : ℝ≥0) : ℝ) := by
    exact_mod_cast le_add_of_nonneg_right t.property
  have hzero : μ (Set.Ioc (0 : ℝ) (u : ℝ)) = 0 :=
    barrierStrategy_dividendMeasure_zero_until_firstUpcrossing
      X x a hx0 hxa ω u hu
  have hunion :
      Set.Ioc (0 : ℝ) (u : ℝ) ∪
        Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ) =
          Set.Ioc (0 : ℝ) ((u + t : ℝ≥0) : ℝ) :=
    Set.Ioc_union_Ioc_eq_Ioc hu0 hut
  have hsub :
      Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ) ⊆
        Set.Ioc (0 : ℝ) ((u + t : ℝ≥0) : ℝ) := by
    intro r hr
    exact ⟨lt_of_le_of_lt hu0 hr.1, hr.2⟩
  have hle : μ (Set.Ioc (0 : ℝ) ((u + t : ℝ≥0) : ℝ)) ≤
      μ (Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ)) := by
    rw [← hunion]
    calc
      μ (Set.Ioc (0 : ℝ) (u : ℝ) ∪
          Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ)) ≤
            μ (Set.Ioc (0 : ℝ) (u : ℝ)) +
            μ (Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ)) :=
        measure_union_le _ _
      _ = _ := by rw [hzero]; simp
  have heq : μ (Set.Ioc (0 : ℝ) ((u + t : ℝ≥0) : ℝ)) =
      μ (Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ)) :=
    le_antisymm hle (measure_mono hsub)
  rw [heq]
  exact barrierStrategy_shifted_runningSup_dividendMeasure_Ioc_unconditional
    X x a hxa ω u hu t