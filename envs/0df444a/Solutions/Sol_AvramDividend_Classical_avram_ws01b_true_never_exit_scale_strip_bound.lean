-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_true_never_exit_scale_strip_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T13:32:02.814565+00:00
-- url     : https://prove2.me/submissions/7415319d-dd44-42d0-9cc1-87a96201ad66

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_le_observation_of_strict_exceedance
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_le_of_strict_lower_gap_observed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- Original Lévy sample paths never leaving the two-sided strip keep Wq bounded by Wq(a). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω)
    (hUp : twoSidedExitUpTime X (a-x) ω = ∞)
    (hDown : twoSidedExitDownTime X (-x) ω = ∞) :
    ∀ t : ℝ≥0, 0 ≤ W (x + X.X t ω) ∧ W (x + X.X t ω) ≤ W a := by
  intro t
  have hu : X.X t ω ≤ a-x := by
    by_contra hn
    have hs : a-x < X.X t ω := lt_of_not_ge hn
    have hh := twoSidedExitUpTime_le_observation_of_strict_exceedance
      X a x ω t hs
    rw [hUp] at hh
    exact (not_lt_of_ge hh) ENNReal.coe_lt_top
  have hl : -x ≤ X.X t ω := by
    by_contra hn
    have hs : X.X t ω < -x := lt_of_not_ge hn
    have hh := twoSidedExitDownTime_le_of_strict_lower_gap_observed
      X x ω t hs
    rw [hDown] at hh
    exact (not_lt_of_ge hh) ENNReal.coe_lt_top
  have h0 : 0 ≤ x + X.X t ω := by linarith
  have ha' : x + X.X t ω ≤ a := by linarith
  exact ⟨hW.2.1 _ h0,
    hW.2.2.2.1 (Set.mem_Ici.mpr h0)
      (Set.mem_Ici.mpr (le_of_lt ha)) ha'⟩
