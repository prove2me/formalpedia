-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_unbounded_future_window_harmonicity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:59:39.095607+00:00
-- url     : https://prove2.me/submissions/284c474f-22ca-4df3-98da-34ab214925c4

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_future_killed_condexp
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_shifted_lower_closed_event_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Actual original-Lévy conditional killed q-scale harmonicity on every
future calendar interval, without a schedule or measurability assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
      0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω)) | 𝓕 s]
      =ᵐ[P] (fun ω => W (x + X.X s ω)) := by
  let T : ℝ≥0 := u - s
  have hT : s + T = u := add_tsub_cancel_of_le hsu
  have hTr : (u : ℝ) - (s : ℝ) = (T : ℝ) := by
    have hc : (s : ℝ) + (T : ℝ) = (u : ℝ) := by
      exact_mod_cast hT
    linarith
  obtain ⟨τ, hCover, hTerminal⟩ :=
    chat04_explicit_shifted_killed_survival_schedule T
  have hB : MeasurableSet {ω : Ω | ∀ v : ℝ≥0, v ≤ T →
      0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)} :=
    avram_root29_01_shifted_lower_closed_event_measurable X x s T
  have hCE := avram_root29_01_unbounded_future_killed_condexp
    X hnbv q hq W hW τ s T hCover hTerminal x hB
  have hEvent :
      {ω : Ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)} =
      {ω : Ω | ∀ v : ℝ≥0, v ≤ T →
        0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)} := by
    ext ω
    constructor
    · intro h v hv
      have hs : s ≤ s + v :=
        le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ v)
      have hu : s + v ≤ u := by
        rw [← hT]
        simpa only [add_comm] using (add_le_add_left hv s)
      exact h (s + v) hs hu
    · intro h v hsv hvu
      have hsub : v - s ≤ T := by
        have hh := tsub_le_tsub_right hvu s
        simpa [T] using hh
      have hh := h (v - s) hsub
      have heq : s + (v - s) = v := add_tsub_cancel_of_le hsv
      simpa only [heq] using hh
  have hReward :
      (fun ω : Ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω)) =
      (fun ω : Ω => Real.exp (-(q * (T : ℝ))) *
        W ((x + X.X s ω) +
          (X.X (s + T) ω - X.X s ω))) := by
    funext ω
    rw [hTr, hT]
    congr 1
    ring
  rw [hEvent, hReward]
  exact hCE
