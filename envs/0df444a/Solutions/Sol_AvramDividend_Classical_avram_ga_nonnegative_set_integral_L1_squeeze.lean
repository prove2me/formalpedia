-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_nonnegative_set_integral_L1_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T07:41:38.042061+00:00
-- url     : https://prove2.me/submissions/a93fce35-677a-427b-b030-76c16d446b8f

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : ℕ → Ω → ℝ)
    (hInt : ∀ m, Integrable (f m) P)
    (hNonneg : ∀ m ω, 0 ≤ f m ω)
    (hVan : Tendsto (fun m => ∫ ω, f m ω ∂P) atTop (nhds (0 : ℝ)))
    (A : Set Ω) :
    Tendsto (fun m => ∫ ω in A, f m ω ∂P) atTop (nhds (0 : ℝ)) := by
  have hmono : P.restrict A ≤ P := Measure.restrict_le_self
  have hLower (m : ℕ) : 0 ≤ ∫ ω in A, f m ω ∂P :=
    integral_nonneg (fun ω => hNonneg m ω)
  have hUpper (m : ℕ) :
      (∫ ω in A, f m ω ∂P) ≤ (∫ ω, f m ω ∂P) :=
    integral_mono_measure hmono
      (Filter.Eventually.of_forall (hNonneg m)) (hInt m)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hVan hLower hUpper
