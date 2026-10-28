-- Prove2me | solution 1 for AvramDividend.Classical.finite_clock_reward_lintegral_eq_sup_caps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:41:14.847984+00:00
-- url     : https://prove2.me/submissions/ec265047-6a1f-4603-81cc-bc6e40793e4c

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (clock : Ω → ℝ≥0∞) (reward : Ω → ℝ≥0∞)
    (hclock : Measurable clock) (hreward : Measurable reward) :
    (∫⁻ ω, if clock ω < ⊤ then reward ω else 0 ∂P) =
      ⨆ n : ℕ, (∫⁻ ω, if clock ω ≤ (n : ℝ≥0∞)
        then reward ω else 0 ∂P) := by
  let f : ℕ → Ω → ℝ≥0∞ :=
    fun n ω => if clock ω ≤ (n : ℝ≥0∞) then reward ω else 0
  have hf : ∀ n, Measurable (f n) := by
    intro n
    exact Measurable.ite (measurableSet_le hclock measurable_const) hreward measurable_const
  have hm : Monotone f := by
    intro i j hij ω
    by_cases hi : clock ω ≤ (i : ℝ≥0∞)
    · have hj : clock ω ≤ (j : ℝ≥0∞) :=
        le_trans hi (by exact_mod_cast hij)
      simp [f, hi, hj]
    · by_cases hj : clock ω ≤ (j : ℝ≥0∞)
      · simp [f, hi, hj]
      · simp [f, hi, hj]
  have hp : (fun ω => if clock ω < ⊤ then reward ω else 0) =
      (fun ω => ⨆ n : ℕ, f n ω) := by
    funext ω
    by_cases ht : clock ω = ⊤
    · simp [f, ht]
    · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ht
      have hfin : clock ω < ⊤ := lt_top_iff_ne_top.mpr ht
      rw [if_pos hfin]
      apply le_antisymm
      · exact le_iSup_of_le n (by simp [f, le_of_lt hn])
      · apply iSup_le
        intro i
        by_cases hi : clock ω ≤ (i : ℝ≥0∞)
        · simp [f, hi]
        · simp [f, hi]
  rw [hp]
  exact lintegral_iSup hf hm
