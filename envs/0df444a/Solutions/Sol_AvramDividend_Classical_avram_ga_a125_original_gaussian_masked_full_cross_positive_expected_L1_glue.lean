-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a125_original_gaussian_masked_full_cross_positive_expected_L1_glue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:21:19.210139+00:00
-- url     : https://prove2.me/submissions/695b050a-351f-42cb-a26f-3cac83c89cf1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

/-- Masked original stopped Gaussian positive error is squeezed by the independent absolute full-cell and positive true crossing-cell expected errors. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U F C : ℕ → Ω → ℝ) (mask : Ω → Prop)
    [DecidablePred mask]
    (hSplit : ∀ m ω, U m ω = F m ω + C m ω)
    (hUI : ∀ m, Integrable (fun ω => if mask ω then max (U m ω) 0 else 0) P)
    (hFI : ∀ m, Integrable (fun ω => |F m ω|) P)
    (hCI : ∀ m, Integrable (fun ω => max (C m ω) 0) P)
    (hFT : Tendsto (fun m => ∫ ω, |F m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hCT : Tendsto (fun m => ∫ ω, max (C m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω,
      (if mask ω then max (U m ω) 0 else 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hPoint (m : ℕ) (ω : Ω) :
      (if mask ω then max (U m ω) 0 else 0) ≤
        |F m ω| + max (C m ω) 0 := by
    by_cases hm : mask ω
    · simp only [if_pos hm, hSplit m ω]
      apply max_le
      · linarith [le_abs_self (F m ω), le_max_left (C m ω) 0]
      · linarith [abs_nonneg (F m ω), le_max_right (C m ω) 0]
    · simp only [if_neg hm]
      positivity
  have hNonneg (m : ℕ) (ω : Ω) :
      0 ≤ (if mask ω then max (U m ω) 0 else 0) := by
    by_cases hm : mask ω
    · simpa only [if_pos hm] using (le_max_right (U m ω) 0)
    · simp only [if_neg hm, le_refl]
  have hPos (m : ℕ) :
      0 ≤ ∫ ω, (if mask ω then max (U m ω) 0 else 0) ∂P :=
    integral_nonneg (hNonneg m)
  have hBound (m : ℕ) :
      (∫ ω, (if mask ω then max (U m ω) 0 else 0) ∂P) ≤
        (∫ ω, |F m ω| ∂P) +
          (∫ ω, max (C m ω) 0 ∂P) := by
    calc
      (∫ ω, (if mask ω then max (U m ω) 0 else 0) ∂P) ≤
          (∫ ω, |F m ω| + max (C m ω) 0 ∂P) :=
        integral_mono (hUI m) ((hFI m).add (hCI m)) (hPoint m)
      _ = (∫ ω, |F m ω| ∂P) +
          (∫ ω, max (C m ω) 0 ∂P) :=
        integral_add (hFI m) (hCI m)
  have hTotal : Tendsto (fun m =>
      (∫ ω, |F m ω| ∂P) +
        (∫ ω, max (C m ω) 0 ∂P)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_zero] using hFT.add hCT
  exact squeeze_zero hPos hBound hTotal
