-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_capped_lower_grid_clock_tendsto_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:50:42.631978+00:00
-- url     : https://prove2.me/submissions/25cba762-6736-4072-a37b-669e40bcd9ef

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.Lattice
import Theorems.Thm_AvramDividend_Classical_chat03_official_lower_grid_clock_tendsto
import Theorems.Thm_AvramDividend_Classical_bv_lower_grid_cap_eq_finite_prefix_ws01c

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set Order AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (ω : Ω) (lower : ℝ) (T : ℝ≥0)
    (mesh : ℕ → ℝ≥0) (M : ℕ → ℕ)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)))
    (hCover : ∀ n, T ≤ (M n : ℝ≥0) * mesh n) :
    Tendsto
      (fun n : ℕ =>
        (⨅ (k : ℕ) (_ : k ≤ M n),
          if X.X ((k : ℝ≥0) * mesh n) ω < lower then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞) ⊓
          (T : ℝ≥0∞))
      atTop
      (𝓝 (twoSidedExitDownTime X lower ω ⊓ (T : ℝ≥0∞))) := by
  have hFull :=
    chat03_official_lower_grid_clock_tendsto X ω lower
      mesh hpos hzero
  have hCapped :
      Tendsto
        (fun n : ℕ =>
          (⨅ k : ℕ,
            if X.X ((k : ℝ≥0) * mesh n) ω < lower then
              (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞) ⊓
            (T : ℝ≥0∞))
        atTop
        (𝓝 (twoSidedExitDownTime X lower ω ⊓ (T : ℝ≥0∞))) :=
    Filter.Tendsto.inf_nhds hFull tendsto_const_nhds
  have hEq (n : ℕ) :
      ((⨅ k : ℕ,
        if X.X ((k : ℝ≥0) * mesh n) ω < lower then
          (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞) ⊓
        (T : ℝ≥0∞)) =
      ((⨅ (k : ℕ) (_ : k ≤ M n),
        if X.X ((k : ℝ≥0) * mesh n) ω < lower then
          (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞) ⊓
        (T : ℝ≥0∞)) :=
    bv_lower_grid_cap_eq_finite_prefix_ws01c
      (fun t => X.X t ω) lower (mesh n) T
      (hpos n) (M n) (hCover n)
  simpa only [hEq] using hCapped