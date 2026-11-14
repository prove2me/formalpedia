-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a133_original_masked_positive_full_cross_expected_L1_eventual_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:28:35.093326+00:00
-- url     : https://prove2.me/submissions/61bab005-96a3-43da-9643-efd447a95dfc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

/-- Eventually integrable original stopped Gaussian masked spatial positive expectation closes from two genuinely one-sided expected source error budgets. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U F C : ℕ → Ω → ℝ) (mask : Ω → Prop) [DecidablePred mask]
    (hSplit : ∀ m ω, U m ω = F m ω + C m ω)
    (hUI : ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => if mask ω then max (U m ω) 0 else 0) P)
    (hFI : ∀ m, Integrable (fun ω => max (F m ω) 0) P)
    (hCI : ∀ m, Integrable (fun ω => max (C m ω) 0) P)
    (hFT : Tendsto (fun m => ∫ ω, max (F m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hCT : Tendsto (fun m => ∫ ω, max (C m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω,
      (if mask ω then max (U m ω) 0 else 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hPoint (m : ℕ) (ω : Ω) :
      (if mask ω then max (U m ω) 0 else 0) ≤
        max (F m ω) 0 + max (C m ω) 0 := by
    by_cases hm : mask ω
    · simp only [if_pos hm, hSplit m ω]
      apply max_le
      · linarith [le_max_left (F m ω) 0, le_max_left (C m ω) 0]
      · linarith [le_max_right (F m ω) 0, le_max_right (C m ω) 0]
    · simp only [if_neg hm]
      positivity
  have hPos (m : ℕ) :
      0 ≤ ∫ ω, (if mask ω then max (U m ω) 0 else 0) ∂P := by
    apply integral_nonneg
    intro ω
    by_cases hm : mask ω
    · simp only [if_pos hm]; exact le_max_right _ 0
    · simp only [if_neg hm]; exact le_refl 0
  obtain ⟨k, hInt⟩ := hUI
  have hBound : ∀ᶠ m in atTop,
      (∫ ω, (if mask ω then max (U m ω) 0 else 0) ∂P) ≤
      (∫ ω, max (F m ω) 0 ∂P) +
        (∫ ω, max (C m ω) 0 ∂P) := by
    filter_upwards [Filter.eventually_ge_atTop k] with m hm
    calc
      (∫ ω, (if mask ω then max (U m ω) 0 else 0) ∂P) ≤
        (∫ ω, max (F m ω) 0 + max (C m ω) 0 ∂P) :=
        integral_mono (hInt m hm) ((hFI m).add (hCI m)) (hPoint m)
      _ = (∫ ω, max (F m ω) 0 ∂P) +
          (∫ ω, max (C m ω) 0 ∂P) :=
        integral_add (hFI m) (hCI m)
  have hTotal : Tendsto (fun m =>
      (∫ ω, max (F m ω) 0 ∂P) +
      (∫ ω, max (C m ω) 0 ∂P)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_zero] using hFT.add hCT
  exact squeeze_zero' (Filter.Eventually.of_forall hPos) hBound hTotal
