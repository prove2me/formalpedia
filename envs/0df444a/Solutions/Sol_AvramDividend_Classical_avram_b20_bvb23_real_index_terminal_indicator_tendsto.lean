-- Prove2me | solution 1 for AvramDividend.Classical.avram_b20_bvb23_real_index_terminal_indicator_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T16:28:43.832403+00:00
-- url     : https://prove2.me/submissions/4528b783-7667-402d-84da-64e7e349c759

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.AtTopBot.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    (T : ℝ) (hT : 0 < T) (τ : ℝ≥0∞) (t : ℝ≥0)
    (ht0 : 0 < t) (htT : (t : ℝ) < T)
    (hτ : (t : ℝ≥0∞) ≠ τ)
    (C : ℝ≥0∞) (b v : ℝ) :
    Tendsto (fun n : ℝ =>
      if 0 < t ∧ (t : ℝ) < T - T / (n + 2) ∧
        (t : ℝ≥0∞) ≤ τ ∧ 0 ≤ b ∧ ENNReal.ofReal b ≤ C
      then v else 0)
      atTop (nhds (if (t : ℝ≥0∞) < τ ∧
        0 ≤ b ∧ ENNReal.ofReal b ≤ C then v else 0)) := by
  have hGap : 0 < T - (t : ℝ) := sub_pos.mpr htT
  have hCut : ∀ᶠ n : ℝ in atTop, (t : ℝ) < T - T / (n + 2) := by
    filter_upwards [eventually_ge_atTop (T / (T - (t : ℝ)))] with n hn
    have hn0 : 0 ≤ n :=
      le_trans (div_nonneg hT.le hGap.le) hn
    have hden : 0 < n + 2 := by linarith
    have hMul : T ≤ (T - (t : ℝ)) * n :=
      by simpa only [mul_comm] using (div_le_iff₀ hGap).mp hn
    have hStrict : T < (T - (t : ℝ)) * (n + 2) := by nlinarith
    have hDiv : T / (n + 2) < T - (t : ℝ) :=
      (div_lt_iff₀ hden).mpr (by nlinarith)
    linarith
  have hLe : ((t : ℝ≥0∞) ≤ τ) ↔ ((t : ℝ≥0∞) < τ) := by
    rw [le_iff_lt_or_eq]
    simp [hτ]
  have hEq : (fun n : ℝ =>
      if 0 < t ∧ (t : ℝ) < T - T / (n + 2) ∧
        (t : ℝ≥0∞) ≤ τ ∧ 0 ≤ b ∧ ENNReal.ofReal b ≤ C
      then v else 0) =ᶠ[atTop]
      (fun _ : ℝ => if (t : ℝ≥0∞) < τ ∧
        0 ≤ b ∧ ENNReal.ofReal b ≤ C then v else 0) := by
    filter_upwards [hCut] with n hn
    simp [ht0, hn, hLe]
  exact tendsto_const_nhds.congr' hEq.symm
