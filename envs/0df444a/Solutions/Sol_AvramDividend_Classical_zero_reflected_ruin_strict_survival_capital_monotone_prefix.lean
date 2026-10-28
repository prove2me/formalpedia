-- Prove2me | solution 1 for AvramDividend.Classical.zero_reflected_ruin_strict_survival_capital_monotone_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:02:43.496137+00:00
-- url     : https://prove2.me/submissions/97ef383f-9192-4de1-b82b-bcc14b036a21

import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Strict survival of the zero reflected barrier forces the actual
    capital path to be nondecreasing on the entire preceding interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (hBefore : (T : ℝ≥0∞) < barrierRuinTime X 0 ω) :
    ∀ s u : ℝ≥0, s ≤ u → u ≤ T → X.X s ω ≤ X.X u ω := by
  obtain ⟨hSupMono, hPathLe⟩ := runningSup_monotone_and_path_le X ω
  have hAtRecord (v : ℝ≥0) (hv : v ≤ T) :
      runningSup X v ω = X.X v ω := by
    have hvENN : (v : ℝ≥0∞) ≤ (T : ℝ≥0∞) := by
      exact_mod_cast hv
    have hvBefore : (v : ℝ≥0∞) < barrierRuinTime X 0 ω :=
      lt_of_le_of_lt hvENN hBefore
    have hNoDrawdown : ¬ 0 < drawdown X v ω := by
      intro hPos
      have hRuinLe : barrierRuinTime X 0 ω ≤ (v : ℝ≥0∞) := by
        unfold barrierRuinTime
        exact iInf_le_of_le v
          (iInf_le (fun (_ : 0 < drawdown X v ω) => (v : ℝ≥0∞)) hPos)
      exact (not_le.mpr hvBefore) hRuinLe
    have hDrawLe : runningSup X v ω - X.X v ω ≤ 0 := by
      simpa only [drawdown, reflectedSup] using le_of_not_gt hNoDrawdown
    have hPath := hPathLe v
    linarith
  intro s u hsu huT
  calc
    X.X s ω = runningSup X s ω := (hAtRecord s (le_trans hsu huT)).symm
    _ ≤ runningSup X u ω := hSupMono hsu
    _ = X.X u ω := hAtRecord u huT
