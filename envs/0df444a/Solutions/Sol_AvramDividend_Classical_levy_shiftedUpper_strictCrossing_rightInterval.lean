-- Prove2me | solution 1 for AvramDividend.Classical.levy_shiftedUpper_strictCrossing_rightInterval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:13:30.268027+00:00
-- url     : https://prove2.me/submissions/a03a395d-4f37-484b-9b63-2d84251c3a29

import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_upper_exit_right_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

/-! Translate the Lévy strict-crossing persistence interval to shifted increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u : ℝ≥0) (upper : ℝ) :
    ∀ s : ℝ≥0, upper < X.X (u + s) ω - X.X u ω →
      ∃ v : ℝ≥0, s < v ∧
        ∀ r : ℝ≥0, s ≤ r → r < v →
          upper < X.X (u + r) ω - X.X u ω := by
  intro s hs
  have hs' : upper + X.X u ω < X.X (u + s) ω :=
    (lt_sub_iff_add_lt).mp hs
  obtain ⟨v, hv, hright⟩ :=
    chat03_strict_upper_exit_right_interval
      X ω (u + s) (upper + X.X u ω) hs'
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
  exact (lt_sub_iff_add_lt).mpr (hright (u + r) hbase hstop)
