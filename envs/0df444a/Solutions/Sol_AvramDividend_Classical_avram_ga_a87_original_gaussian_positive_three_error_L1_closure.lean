-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a87_original_gaussian_positive_three_error_L1_closure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:11:05.983811+00:00
-- url     : https://prove2.me/submissions/8f645477-caff-4209-924c-d208cc657cca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

/-- A positive-part expected residual is controlled by the three independently vanishing absolute-L1 source errors. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U A B C : ℕ → Ω → ℝ)
    (hUi : ∀ m, Integrable (fun ω => max (U m ω) 0) P)
    (hAi : ∀ m, Integrable (fun ω => |A m ω|) P)
    (hBi : ∀ m, Integrable (fun ω => |B m ω|) P)
    (hCi : ∀ m, Integrable (fun ω => |C m ω|) P)
    (hDom : ∀ m ω, max (U m ω) 0 ≤
      |A m ω| + |B m ω| + |C m ω|)
    (hAt : Tendsto (fun m => ∫ ω, |A m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hBt : Tendsto (fun m => ∫ ω, |B m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hCt : Tendsto (fun m => ∫ ω, |C m ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, max (U m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hPos (m : ℕ) : 0 ≤ (∫ ω, max (U m ω) 0 ∂P) :=
    integral_nonneg (fun ω => le_max_right (U m ω) 0)
  have hBound (m : ℕ) :
      (∫ ω, max (U m ω) 0 ∂P) ≤
        (∫ ω, |A m ω| ∂P) +
          (∫ ω, |B m ω| ∂P) +
            (∫ ω, |C m ω| ∂P) := by
    calc
      (∫ ω, max (U m ω) 0 ∂P) ≤
          (∫ ω, |A m ω| + |B m ω| + |C m ω| ∂P) :=
        integral_mono (hUi m)
          (((hAi m).add (hBi m)).add (hCi m))
          (hDom m)
      _ = (∫ ω, |A m ω| ∂P) +
            (∫ ω, |B m ω| ∂P) +
              (∫ ω, |C m ω| ∂P) := by
        have hAB : (∫ ω, |A m ω| + |B m ω| ∂P) =
            (∫ ω, |A m ω| ∂P) + (∫ ω, |B m ω| ∂P) :=
          integral_add (hAi m) (hBi m)
        have hABC : (∫ ω, (|A m ω| + |B m ω|) + |C m ω| ∂P) =
            (∫ ω, |A m ω| + |B m ω| ∂P) +
              (∫ ω, |C m ω| ∂P) :=
          integral_add ((hAi m).add (hBi m)) (hCi m)
        exact hABC.trans (congrArg (fun z : ℝ =>
          z + (∫ ω, |C m ω| ∂P)) hAB)
  have hTotal : Tendsto
      (fun m => (∫ ω, |A m ω| ∂P) +
        (∫ ω, |B m ω| ∂P) + (∫ ω, |C m ω| ∂P))
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_zero] using ((hAt.add hBt).add hCt)
  exact squeeze_zero hPos hBound hTotal
