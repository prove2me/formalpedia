-- Prove2me | solution 1 for AvramDividend.Classical.chat04_negative_running_infimum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:46:28.895393+00:00
-- url     : https://prove2.me/submissions/44a3c094-3e49-4adf-9ccd-d656da8e86b3

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ω : Ω) :
    0 ≤ -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} := by
  let S : Set ℝ :=
    {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}
  have hb : BddBelow S := levy_path_bddBelow_finite_horizon X t ω
  have hmem : (0 : ℝ) ∈ S := by
    exact ⟨0, bot_le, (X.X_zero ω).symm⟩
  have hle : sInf S ≤ 0 := csInf_le hb hmem
  change 0 ≤ -sInf S
  linarith
