-- Prove2me | solution 1 for AvramDividend.Classical.levy_shiftedLower_strictCrossing_rightInterval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:13:33.270369+00:00
-- url     : https://prove2.me/submissions/943d214f-cd26-4cd5-9171-e58c83726df5

import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_lower_exit_right_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

/-! Shift strict downward passage persistence to a future increment path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u : ℝ≥0) (lower : ℝ) :
    ∀ s : ℝ≥0, X.X (u + s) ω - X.X u ω < lower →
      ∃ v : ℝ≥0, s < v ∧
        ∀ r : ℝ≥0, s ≤ r → r < v →
          X.X (u + r) ω - X.X u ω < lower := by
  intro s hs
  have hs' : X.X (u + s) ω < lower + X.X u ω :=
    (sub_lt_iff_lt_add).mp hs
  obtain ⟨v, hv, hright⟩ :=
    chat03_strict_lower_exit_right_interval
      X ω (u + s) (lower + X.X u ω) hs'
  have huv : u ≤ v := by
    have hu : u ≤ u + s := le_add_of_nonneg_right (by exact zero_le)
    exact hu.trans hv.le
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
  exact (sub_lt_iff_lt_add).mpr (hright (u + r) hbase hstop)
