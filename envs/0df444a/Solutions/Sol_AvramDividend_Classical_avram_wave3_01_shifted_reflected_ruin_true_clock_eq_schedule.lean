-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_shifted_reflected_ruin_true_clock_eq_schedule
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:54:05.136766+00:00
-- url     : https://prove2.me/submissions/5c8199c2-fe82-4297-a450-b980c09fa67e

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_rightInterval_lower_strictExit_eq_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

/-- The original reflected Lévy ruin clock seen from any shifted time
    is exactly its genuine rational-schedule strict-crossing infimum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u : ℝ≥0) (a : ℝ) :
    (⨅ i : {t : ℝ≥0 //
      X.X (u + t) ω - runningSup X (u + t) ω < -a},
        (i.1 : ℝ≥0∞)) =
    (⨅ j : ℕ,
      if X.X (u + (((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹))) ω -
         runningSup X (u + (((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹))) ω < -a
      then ((((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) : ℝ≥0∞)
      else ⊤) := by
  classical
  have hOrig :
      ∀ s : ℝ≥0,
        X.X s ω - runningSup X s ω < -a →
        ∃ v : ℝ≥0, s < v ∧
          ∀ r : ℝ≥0, s ≤ r → r < v →
            X.X r ω - runningSup X r ω < -a := by
    intro s hs
    have hcont : ContinuousWithinAt
        (fun t : ℝ≥0 => X.X t ω - runningSup X t ω)
        (Ici s) s :=
      (X.rightCont ω s).sub
        ((runningSup_continuous_actual X ω).continuousWithinAt)
    have hev_ge : ∀ᶠ r in 𝓝[≥] s,
        X.X r ω - runningSup X r ω < -a :=
      hcont.tendsto.eventually (Iio_mem_nhds hs)
    have hev_gt : ∀ᶠ r in 𝓝[>] s,
        X.X r ω - runningSup X r ω < -a :=
      hev_ge.filter_mono (nhdsWithin_mono s Ioi_subset_Ici_self)
    rcases mem_nhdsGT_iff_exists_Ioo_subset.mp
        (show {r : ℝ≥0 | X.X r ω - runningSup X r ω < -a} ∈
          𝓝[>] s from hev_gt) with ⟨v, hsv, hv⟩
    refine ⟨v, hsv, ?_⟩
    intro r hsr hrv
    rcases eq_or_lt_of_le hsr with heq | hlt
    · simpa [heq] using hs
    · exact hv ⟨hlt, hrv⟩
  let g : ℝ≥0 → ℝ := fun t =>
    X.X (u + t) ω - runningSup X (u + t) ω
  have hShift : ∀ s : ℝ≥0, g s < -a →
      ∃ v : ℝ≥0, s < v ∧
        ∀ r : ℝ≥0, s ≤ r → r < v → g r < -a := by
    intro s hs
    obtain ⟨v, hv, hRight⟩ :=
      hOrig (u + s) (by simpa only [g] using hs)
    have huv : u ≤ v := by
      exact (le_add_of_nonneg_right (by exact zero_le)).trans hv.le
    have hsum : u + (v - u) = v := add_tsub_cancel_of_le huv
    have hsv : s < v - u := by
      apply lt_of_add_lt_add_left
      calc
        u + s < v := hv
        _ = u + (v - u) := hsum.symm
    refine ⟨v - u, hsv, ?_⟩
    intro r hsr hrv
    have hbase : u + s ≤ u + r := by
      simpa only [add_comm] using (add_le_add_right hsr u)
    have hstop : u + r < v := by
      calc
        u + r < u + (v - u) := by
          simpa only [add_comm] using (add_lt_add_right hrv u)
        _ = v := hsum
    exact hRight (u + r) hbase hstop
  simpa only [g] using
    (rightInterval_lower_strictExit_eq_schedule g (-a) hShift)
