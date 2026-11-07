-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f8_integrable_clock_family_expected_iff_signed_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:08:39.855206+00:00
-- url     : https://prove2.me/submissions/c53f37b8-45c8-4041-b802-61be2e1e6eaf

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (hFI : ∀ k, Integrable (F k) P)
    (b : ℝ) :
    (∀ k, (∫ ω, F k ω ∂P) ≤ b) ↔
      ∃ M : ℕ → Ω → ℝ,
        (∀ k, Integrable (M k) P) ∧
        (∀ k, (∫ ω, M k ω ∂P) ≤ 0) ∧
        (∀ k, ∀ᵐ ω ∂P, F k ω ≤ b + M k ω) := by
  constructor
  · intro hbound
    refine ⟨fun k ω => F k ω - b, ?_, ?_, ?_⟩
    · intro k
      exact (hFI k).sub (integrable_const b)
    · intro k
      change (∫ ω, F k ω - b ∂P) ≤ 0
      calc
        _ = (∫ ω, F k ω ∂P) - (∫ ω, b ∂P) :=
          integral_sub (hFI k) (integrable_const b)
        _ = (∫ ω, F k ω ∂P) - b := by simp
        _ ≤ 0 := by linarith [hbound k]
    · intro k
      filter_upwards [] with ω
      change F k ω ≤ b + (F k ω - b)
      linarith
  · rintro ⟨M, hMI, hMnonpos, hupper⟩
    intro k
    have hi : (∫ ω, F k ω ∂P) ≤
        ∫ ω, (b + M k ω) ∂P :=
      integral_mono_ae (hFI k) ((integrable_const b).add (hMI k)) (hupper k)
    calc
      (∫ ω, F k ω ∂P) ≤ ∫ ω, (b + M k ω) ∂P := hi
      _ = (∫ ω, b ∂P) + (∫ ω, M k ω ∂P) :=
        integral_add (integrable_const b) (hMI k)
      _ = b + (∫ ω, M k ω ∂P) := by simp
      _ ≤ b := by linarith [hMnonpos k]
