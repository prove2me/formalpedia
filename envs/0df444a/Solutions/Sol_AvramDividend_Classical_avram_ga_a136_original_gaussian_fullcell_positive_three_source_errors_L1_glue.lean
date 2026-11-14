-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a136_original_gaussian_fullcell_positive_three_source_errors_L1_glue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:30:52.603489+00:00
-- url     : https://prove2.me/submissions/c4db19b7-f6eb-4f5b-a4d9-66bc6e2f6c95

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

/-- Original physical Gaussian full-cell expected positive error closes from source Taylor, raw-centred and discount components without absolute tail assumptions. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F T B C : ℕ → Ω → ℝ)
    (hSplit : ∀ m ω, F m ω = T m ω + B m ω + C m ω)
    (hFI : ∀ m, Integrable (fun ω => max (F m ω) 0) P)
    (hTI : ∀ m, Integrable (fun ω => max (T m ω) 0) P)
    (hBI : ∀ m, Integrable (fun ω => |B m ω|) P)
    (hCI : ∀ m, Integrable (fun ω => max (C m ω) 0) P)
    (hTt : Tendsto (fun m => ∫ ω, max (T m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hBt : Tendsto (fun m => ∫ ω, |B m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hCt : Tendsto (fun m => ∫ ω, max (C m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, max (F m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hPoint (m : ℕ) (ω : Ω) :
      max (F m ω) 0 ≤
        max (T m ω) 0 + |B m ω| + max (C m ω) 0 := by
    rw [hSplit m ω]
    apply max_le
    · linarith [le_max_left (T m ω) 0, le_abs_self (B m ω),
        le_max_left (C m ω) 0]
    · linarith [le_max_right (T m ω) 0,
        abs_nonneg (B m ω), le_max_right (C m ω) 0]
  have hPos (m : ℕ) :
      0 ≤ ∫ ω, max (F m ω) 0 ∂P :=
    integral_nonneg (fun ω => le_max_right _ 0)
  have hUpper (m : ℕ) :
      (∫ ω, max (F m ω) 0 ∂P) ≤
      (∫ ω, max (T m ω) 0 ∂P) +
        (∫ ω, |B m ω| ∂P) +
        (∫ ω, max (C m ω) 0 ∂P) := by
    calc
      (∫ ω, max (F m ω) 0 ∂P) ≤
          (∫ ω, (max (T m ω) 0 + |B m ω|) +
            max (C m ω) 0 ∂P) :=
        integral_mono (hFI m)
          (((hTI m).add (hBI m)).add (hCI m)) (hPoint m)
      _ = (∫ ω, max (T m ω) 0 ∂P) +
          (∫ ω, |B m ω| ∂P) +
          (∫ ω, max (C m ω) 0 ∂P) := by
        have hTB : (∫ ω, max (T m ω) 0 + |B m ω| ∂P) =
            (∫ ω, max (T m ω) 0 ∂P) + (∫ ω, |B m ω| ∂P) :=
          integral_add (hTI m) (hBI m)
        have hTBC : (∫ ω, (max (T m ω) 0 + |B m ω|) +
              max (C m ω) 0 ∂P) =
            (∫ ω, max (T m ω) 0 + |B m ω| ∂P) +
              (∫ ω, max (C m ω) 0 ∂P) :=
          integral_add ((hTI m).add (hBI m)) (hCI m)
        exact hTBC.trans (congrArg (fun z : ℝ =>
          z + (∫ ω, max (C m ω) 0 ∂P)) hTB)
  have hTotal : Tendsto (fun m =>
      (∫ ω, max (T m ω) 0 ∂P) +
        (∫ ω, |B m ω| ∂P) +
        (∫ ω, max (C m ω) 0 ∂P)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_zero] using (hTt.add hBt).add hCt
  exact squeeze_zero hPos hUpper hTotal
