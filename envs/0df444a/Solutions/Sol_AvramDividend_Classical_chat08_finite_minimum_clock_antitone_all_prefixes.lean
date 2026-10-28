-- Prove2me | solution 1 for AvramDividend.Classical.chat08_finite_minimum_clock_antitone_all_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:08:03.234405+00:00
-- url     : https://prove2.me/submissions/ecf4ab49-b9c1-4c0e-8306-cfbefbc35246

import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_clock_antitone_prefix
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-! The minimum clock is antitone for any pair of finite-prefix lengths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (τ : ℕ → Ω → WithTop ℝ≥0) (m n : ℕ) (hmn : m ≤ n) (ω : Ω) :
    (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun k σ ω => min (τ k ω) (σ ω)) n) ω ≤
    (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun k σ ω => min (τ k ω) (σ ω)) m) ω := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
      exact (chat08_finite_minimum_clock_antitone_prefix τ n ω).trans ih
