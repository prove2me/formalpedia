-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva43_signed_B_integrable_of_one_sided_integrable_error
-- status  : ACCEPTED   (disprove)
-- author  : @garyholm
-- created : 2026-11-18T03:05:43.524208+00:00
-- url     : https://prove2.me/submissions/236a2469-1d84-4cc3-92ea-8a407d0903b5

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Tactic.Linarith
set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F M B E : Ω → ℝ) (a : ℝ)
    (hFI : Integrable F P)
    (hMI : Integrable M P)
    (hEI : Integrable (fun ω => max (E ω) 0) P)
    (hBmeas : AEStronglyMeasurable B P)
    (hBnonpos : ∀ᵐ ω ∂P, B ω ≤ 0)
    (hBound : ∀ᵐ ω ∂P,
      F ω ≤ a + M ω + B ω + max (E ω) 0),
    Integrable B P) := by
  intro h
  have hI := h (Ω := ℝ) volume (fun _ => 0) (fun _ => 0) (fun _ => -1) (fun _ => 0) 1
    (integrable_zero _ _ _) (integrable_zero _ _ _) (by simp)
    aestronglyMeasurable_const (by simp) (by simp)
  have : Integrable (fun _ : ℝ => (1 : ℝ)) volume := by simpa using hI.neg
  rw [integrable_const_iff] at this
  simp only [one_ne_zero, false_or] at this
  have h2 := measure_lt_top (volume : Measure ℝ) Set.univ
  rw [Real.volume_univ] at h2
  exact lt_irrefl _ h2
