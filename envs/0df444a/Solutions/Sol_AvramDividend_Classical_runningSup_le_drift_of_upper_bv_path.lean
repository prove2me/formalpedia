-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_le_drift_of_upper_bv_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:24:28.335794+00:00
-- url     : https://prove2.me/submissions/aa51d520-0620-470a-a322-817e0ee7638d

import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Mathlib.Data.NNReal.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A drift bound for all past capital values bounds the original record process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0)
    (hDrift : 0 ≤ X.drift)
    (hPath : ∀ u : ℝ≥0, u ≤ t →
      X.X u ω ≤ X.drift * (u : ℝ)) :
    runningSup X t ω ≤ X.drift * (t : ℝ) := by
  rw [(runningSup_eq_rawSup_nonneg X t ω).1]
  letI : Nonempty (Set.Icc (0 : ℝ≥0) t) :=
    ⟨⟨t, ⟨bot_le, le_rfl⟩⟩⟩
  apply ciSup_le
  intro s
  have hs := hPath s.1 s.2.2
  have hst : (s.1 : ℝ) ≤ (t : ℝ) :=
    NNReal.coe_le_coe.mpr s.2.2
  exact hs.trans (mul_le_mul_of_nonneg_left hst hDrift)
