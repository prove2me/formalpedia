-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_real_mark_sequence_liminf_extension_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:45:11.356189+00:00
-- url     : https://prove2.me/submissions/648734e4-b739-41ec-9bf0-25fddd0efb6e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- A real mark sequence has a measurable globally defined lower-limit extension. -/
theorem solution
    (f : ℕ → (ℝ≥0 → ℝ) → ℝ)
    (hf : ∀ n : ℕ, Measurable (f n)) :
    Measurable (fun Y : ℝ≥0 → ℝ =>
      EReal.toReal (⨆ m : ℕ, ⨅ n : ℕ,
        if m ≤ n then (f n Y : EReal) else ⊤)) := by
  classical
  have hE (n : ℕ) :
      Measurable (fun Y : ℝ≥0 → ℝ => (f n Y : EReal)) :=
    measurable_coe_real_ereal.comp (hf n)
  have hPiece (m n : ℕ) :
      Measurable (fun Y : ℝ≥0 → ℝ =>
        if m ≤ n then (f n Y : EReal) else ⊤) := by
    by_cases hmn : m ≤ n
    · simpa [hmn] using hE n
    · simpa [hmn] using
        (measurable_const : Measurable
          (fun _ : ℝ≥0 → ℝ => (⊤ : EReal)))
  have hInf (m : ℕ) :
      Measurable (fun Y : ℝ≥0 → ℝ =>
        ⨅ n : ℕ, if m ≤ n then (f n Y : EReal) else ⊤) :=
    Measurable.iInf (hPiece m)
  have hSup :
      Measurable (fun Y : ℝ≥0 → ℝ =>
        ⨆ m : ℕ, ⨅ n : ℕ,
          if m ≤ n then (f n Y : EReal) else ⊤) :=
    Measurable.iSup hInf
  exact hSup.ereal_toReal
