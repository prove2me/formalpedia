-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_exact_jump_mark_measurable_extension_from_sample_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:03:08.274312+00:00
-- url     : https://prove2.me/submissions/c2bb094c-8ce6-4eb9-8c7e-abead243383d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_real_mark_sequence_liminf_extension_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_ereal_lower_tail_envelope_recovers_finite_mark_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact irrational-time jump marks have globally measurable sample extensions. -/
theorem solution
    (t : (ℝ≥0 → ℝ) → ℝ≥0)
    (right left : ℕ → (ℝ≥0 → ℝ) → ℝ)
    (hRightMeas : ∀ n : ℕ, Measurable (right n))
    (hLeftMeas : ∀ n : ℕ, Measurable (left n)) :
    ∃ mark : (ℝ≥0 → ℝ) → ℝ,
      Measurable mark ∧
      ∀ Y : ℝ≥0 → ℝ,
        Tendsto (fun n : ℕ => right n Y) atTop (𝓝 (Y (t Y))) →
        Tendsto (fun n : ℕ => left n Y) atTop
          (𝓝 (Function.leftLim Y (t Y))) →
        mark Y = Y (t Y) - Function.leftLim Y (t Y) := by
  let R : (ℝ≥0 → ℝ) → ℝ := fun Y =>
    EReal.toReal (⨆ m : ℕ, ⨅ n : ℕ,
      if m ≤ n then (right n Y : EReal) else ⊤)
  let L : (ℝ≥0 → ℝ) → ℝ := fun Y =>
    EReal.toReal (⨆ m : ℕ, ⨅ n : ℕ,
      if m ≤ n then (left n Y : EReal) else ⊤)
  have hRM : Measurable R :=
    avram_wave7_01_real_mark_sequence_liminf_extension_measurable
      right hRightMeas
  have hLM : Measurable L :=
    avram_wave7_01_real_mark_sequence_liminf_extension_measurable
      left hLeftMeas
  refine ⟨fun Y => R Y - L Y, hRM.sub hLM, ?_⟩
  intro Y hRight hLeft
  have hRightE : Tendsto (fun n : ℕ => (right n Y : EReal))
      atTop (𝓝 ((Y (t Y) : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto (Y (t Y))).comp hRight
  have hLeftE : Tendsto (fun n : ℕ => (left n Y : EReal))
      atTop (𝓝 ((Function.leftLim Y (t Y) : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto (Function.leftLim Y (t Y))).comp hLeft
  have hREq : R Y = Y (t Y) :=
    avram_wave7_01_ereal_lower_tail_envelope_recovers_finite_mark_limit
      (fun n : ℕ => (right n Y : EReal)) (Y (t Y)) hRightE
  have hLEq : L Y = Function.leftLim Y (t Y) :=
    avram_wave7_01_ereal_lower_tail_envelope_recovers_finite_mark_limit
      (fun n : ℕ => (left n Y : EReal))
      (Function.leftLim Y (t Y)) hLeftE
  change R Y - L Y = Y (t Y) - Function.leftLim Y (t Y)
  rw [hREq, hLEq]
