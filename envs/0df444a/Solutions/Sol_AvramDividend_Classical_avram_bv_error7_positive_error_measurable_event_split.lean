-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_positive_error_measurable_event_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:57:57.523204+00:00
-- url     : https://prove2.me/submissions/ad105bd7-ffbe-42e1-abe5-44a55289d8d2

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped Classical
noncomputable section

/-- Split an integrable positive source error exactly into its measurable
interior-event contribution and complementary contact/boundary tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (s : Set Ω) (hs : MeasurableSet s)
    (E : Ω → ℝ)
    (hPos : Integrable (fun ω => max (E ω) 0) P) :
    (Integrable (fun ω => max (if ω ∈ s then E ω else 0) 0) P) ∧
    (Integrable (fun ω => max (if ω ∉ s then E ω else 0) 0) P) ∧
    (∫ ω, max (E ω) 0 ∂P) =
      (∫ ω, max (if ω ∈ s then E ω else 0) 0 ∂P) +
      (∫ ω, max (if ω ∉ s then E ω else 0) 0 ∂P) := by
  have hS : (fun ω => max (if ω ∈ s then E ω else 0) 0) =
      s.indicator (fun ω => max (E ω) 0) := by
    funext ω
    by_cases hω : ω ∈ s <;> simp [Set.indicator, hω]
  have hT : (fun ω => max (if ω ∉ s then E ω else 0) 0) =
      sᶜ.indicator (fun ω => max (E ω) 0) := by
    funext ω
    by_cases hω : ω ∈ s <;> simp [Set.indicator, hω]
  have hSI : Integrable
      (fun ω => max (if ω ∈ s then E ω else 0) 0) P := by
    rw [hS]
    exact MeasureTheory.Integrable.indicator hPos hs
  have hTI : Integrable
      (fun ω => max (if ω ∉ s then E ω else 0) 0) P := by
    rw [hT]
    exact MeasureTheory.Integrable.indicator hPos hs.compl
  refine ⟨hSI, hTI, ?_⟩
  have hSplit : (fun ω => max (E ω) 0) =
      (fun ω => max (if ω ∈ s then E ω else 0) 0 +
        max (if ω ∉ s then E ω else 0) 0) := by
    funext ω
    by_cases hω : ω ∈ s <;> simp [hω]
  conv_lhs => rw [hSplit]
  exact integral_add hSI hTI
