-- Prove2me | solution 1 for AvramDividend.Classical.chat08_finite_minimum_le_any_included_observation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:23:16.892986+00:00
-- url     : https://prove2.me/submissions/d7a4edb0-9349-4e01-9b6d-e6181ca09647

import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_clock_antitone_all_prefixes
import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_le_new_observation
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-! A finite first-detection clock is bounded by every clock in its observation prefix. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (τ : ℕ → Ω → WithTop ℝ≥0) (n k : ℕ) (hk : k < n) (ω : Ω) :
    (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun j σ ω => min (τ j ω) (σ ω)) n) ω ≤ τ k ω := by
  have hk' : k + 1 ≤ n := Nat.succ_le_of_lt hk
  calc
    (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun j σ ω => min (τ j ω) (σ ω)) n) ω ≤
        (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun j σ ω => min (τ j ω) (σ ω)) (k + 1)) ω :=
          chat08_finite_minimum_clock_antitone_all_prefixes τ (k + 1) n hk' ω
    _ ≤ τ k ω := chat08_finite_minimum_le_new_observation τ k ω
