-- Prove2me | solution 1 for AvramDividend.Classical.chat08_finite_minimum_clock_top_iff_all_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:16:54.354989+00:00
-- url     : https://prove2.me/submissions/051e2c18-45bd-4e71-98d5-a13fee12ee8e

import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_clock_antitone_all_prefixes
import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_le_new_observation
import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_clock_eq_top_of_all_top
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-! Infinity of a finite-prefix clock is equivalent to no detected observation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (τ : ℕ → Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) :
    (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun j σ ω => min (τ j ω) (σ ω)) n) ω = ⊤ ↔
      ∀ k : ℕ, k < n → τ k ω = ⊤ := by
  constructor
  · intro h k hk
    have hkn : k + 1 ≤ n := Nat.succ_le_of_lt hk
    have hprefix := chat08_finite_minimum_clock_antitone_all_prefixes
      τ (k + 1) n hkn ω
    have hobservation := chat08_finite_minimum_le_new_observation τ k ω
    have htop : (⊤ : WithTop ℝ≥0) ≤ τ k ω := by
      calc
        (⊤ : WithTop ℝ≥0) = (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun j σ ω => min (τ j ω) (σ ω)) n) ω := h.symm
        _ ≤ (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun j σ ω => min (τ j ω) (σ ω)) (k + 1)) ω := hprefix
        _ ≤ τ k ω := hobservation
    exact top_unique htop
  · intro h
    exact chat08_finite_minimum_clock_eq_top_of_all_top τ n ω h
