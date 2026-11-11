-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva21_physical_positive_error_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:13:09.697146+00:00
-- url     : https://prove2.me/submissions/6a389a76-9562-445c-a03b-3818854c3765

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (E err : ℕ → ℝ)
    (hBound : ∀ n, E n ≤ err n)
    (hErrNonneg : ∀ n, 0 ≤ err n)
    (hErr : Tendsto err atTop (𝓝 0)) :
    Tendsto (fun n => max (E n) 0) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => le_max_right (E n) 0)
    (fun n => max_le_iff.mpr ⟨hBound n, hErrNonneg n⟩)
    hErr
