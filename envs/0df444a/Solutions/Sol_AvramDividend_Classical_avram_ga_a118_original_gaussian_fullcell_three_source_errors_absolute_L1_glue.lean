-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a118_original_gaussian_fullcell_three_source_errors_absolute_L1_glue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:23:12.211662+00:00
-- url     : https://prove2.me/submissions/487fefd0-58d2-4bbc-ab4a-b3d710895f86

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

/-- The three actual Gaussian full-cell Taylor, drift-cross and discount errors control its absolute spatial residual in expected L1. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F A B C : ℕ → Ω → ℝ)
    (hSplit : ∀ m ω, F m ω = A m ω + B m ω + C m ω)
    (hFI : ∀ m, Integrable (fun ω => |F m ω|) P)
    (hAI : ∀ m, Integrable (fun ω => |A m ω|) P)
    (hBI : ∀ m, Integrable (fun ω => |B m ω|) P)
    (hCI : ∀ m, Integrable (fun ω => |C m ω|) P)
    (hAt : Tendsto (fun m => ∫ ω, |A m ω| ∂P) atTop (𝓝 (0 : ℝ)))
    (hBt : Tendsto (fun m => ∫ ω, |B m ω| ∂P) atTop (𝓝 (0 : ℝ)))
    (hCt : Tendsto (fun m => ∫ ω, |C m ω| ∂P) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, |F m ω| ∂P) atTop (𝓝 (0 : ℝ)) := by
  have hPoint (m : ℕ) (ω : Ω) :
      |F m ω| ≤ |A m ω| + |B m ω| + |C m ω| := by
    rw [hSplit m ω]
    have h1 : |A m ω + B m ω| ≤ |A m ω| + |B m ω| :=
      abs_add_le _ _
    have h2 : |A m ω + B m ω + C m ω| ≤
        |A m ω + B m ω| + |C m ω| := abs_add_le _ _
    linarith only [h1,h2]
  have hPos (m : ℕ) : 0 ≤ (∫ ω, |F m ω| ∂P) :=
    integral_nonneg (fun ω => abs_nonneg _)
  have hBound (m : ℕ) :
      (∫ ω, |F m ω| ∂P) ≤
        (∫ ω, |A m ω| ∂P) +
          (∫ ω, |B m ω| ∂P) + (∫ ω, |C m ω| ∂P) := by
    calc
      (∫ ω, |F m ω| ∂P) ≤
          (∫ ω, (|A m ω| + |B m ω|) + |C m ω| ∂P) :=
        integral_mono (hFI m)
          (((hAI m).add (hBI m)).add (hCI m)) (hPoint m)
      _ = (∫ ω, |A m ω| ∂P) +
            (∫ ω, |B m ω| ∂P) + (∫ ω, |C m ω| ∂P) := by
        have hAB : (∫ ω, |A m ω| + |B m ω| ∂P) =
            (∫ ω, |A m ω| ∂P) + (∫ ω, |B m ω| ∂P) :=
          integral_add (hAI m) (hBI m)
        have hABC : (∫ ω, (|A m ω| + |B m ω|) + |C m ω| ∂P) =
            (∫ ω, |A m ω| + |B m ω| ∂P) +
              (∫ ω, |C m ω| ∂P) :=
          integral_add ((hAI m).add (hBI m)) (hCI m)
        exact hABC.trans (congrArg (fun z : ℝ =>
          z + (∫ ω, |C m ω| ∂P)) hAB)
  have hTotal : Tendsto (fun m =>
      (∫ ω, |A m ω| ∂P) +
        (∫ ω, |B m ω| ∂P) + (∫ ω, |C m ω| ∂P))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_zero] using (hAt.add hBt).add hCt
  exact squeeze_zero hPos hBound hTotal
