-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB44_native_brownian_centered_continuous_path_lift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:04:50.155808+00:00
-- url     : https://prove2.me/submissions/c545f8e8-2df7-4d09-89fd-4c31073c8627

import Mathlib
import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_zero_continuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Every native centered Brownian path has a unit-interval continuous lift. -/
theorem solution :
    ∃ B : (ℝ≥0 → ℝ) → C(unitInterval, ℝ),
      ∀ (ω : ℝ≥0 → ℝ) (t : unitInterval),
        B ω t =
          ProbabilityTheory.brownian (⟨(t : ℝ), t.2.1⟩ : ℝ≥0) ω -
          ProbabilityTheory.brownian 0 ω := by
  classical
  let B : (ℝ≥0 → ℝ) → C(unitInterval, ℝ) := fun ω =>
    ⟨(fun t : unitInterval =>
      ProbabilityTheory.brownian (⟨(t : ℝ), t.2.1⟩ : ℝ≥0) ω -
        ProbabilityTheory.brownian 0 ω), by
      have hb := (canonical_drifted_brownian_zero_continuous ω).2
      have ht : Continuous (fun s : ℝ≥0 => (s : ℝ)) := by fun_prop
      have hc : Continuous (fun s : ℝ≥0 =>
          ProbabilityTheory.brownian s ω -
            ProbabilityTheory.brownian 0 ω) := by
        have hf :
            (fun s : ℝ≥0 =>
              (ProbabilityTheory.brownian s ω -
                ProbabilityTheory.brownian 0 ω - (s : ℝ)) + (s : ℝ)) =
            (fun s : ℝ≥0 =>
              ProbabilityTheory.brownian s ω -
                ProbabilityTheory.brownian 0 ω) := by
          funext s
          ring
        rw [← hf]
        exact hb.add ht
      have hi : Continuous (fun t : unitInterval =>
          (⟨(t : ℝ), t.2.1⟩ : ℝ≥0)) := by fun_prop
      exact hc.comp hi⟩
  exact ⟨B, fun _ _ => rfl⟩
