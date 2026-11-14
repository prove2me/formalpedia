-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a114_original_gaussian_full_cross_spatial_positive_L1_glue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:46:29.574194+00:00
-- url     : https://prove2.me/submissions/da3760d7-a1a0-4890-ac5c-18d81327a3c7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

/-- A true clipped original Gaussian stopped spatial residual closes in expected positive L1 from the independently vanishing absolute full-cell and one-sided single crossing-cell components. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U F C : ℕ → Ω → ℝ)
    (hSplit : ∀ m ω, U m ω = F m ω + C m ω)
    (hUI : ∀ m, Integrable (fun ω => max (U m ω) 0) P)
    (hFI : ∀ m, Integrable (fun ω => |F m ω|) P)
    (hCI : ∀ m, Integrable (fun ω => max (C m ω) 0) P)
    (hFT : Tendsto (fun m => ∫ ω, |F m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hCT : Tendsto (fun m => ∫ ω, max (C m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, max (U m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hPoint (m : ℕ) (ω : Ω) :
      max (U m ω) 0 ≤ |F m ω| + max (C m ω) 0 := by
    rw [hSplit m ω]
    apply max_le
    · linarith [le_abs_self (F m ω),
        le_max_left (C m ω) 0]
    · linarith [abs_nonneg (F m ω),
        le_max_right (C m ω) 0]
  have hPos (m : ℕ) :
      0 ≤ ∫ ω, max (U m ω) 0 ∂P :=
    integral_nonneg (fun ω => le_max_right (U m ω) 0)
  have hBound (m : ℕ) :
      (∫ ω, max (U m ω) 0 ∂P) ≤
      (∫ ω, |F m ω| ∂P) +
        (∫ ω, max (C m ω) 0 ∂P) := by
    calc
      (∫ ω, max (U m ω) 0 ∂P) ≤
        (∫ ω, |F m ω| + max (C m ω) 0 ∂P) :=
        integral_mono (hUI m) ((hFI m).add (hCI m)) (hPoint m)
      _ = (∫ ω, |F m ω| ∂P) +
        (∫ ω, max (C m ω) 0 ∂P) :=
        integral_add (hFI m) (hCI m)
  have hSum := hFT.add hCT
  have hTotal : Tendsto
      (fun m => (∫ ω, |F m ω| ∂P) +
        (∫ ω, max (C m ω) 0 ∂P)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_zero] using hSum
  exact squeeze_zero hPos hBound hTotal
