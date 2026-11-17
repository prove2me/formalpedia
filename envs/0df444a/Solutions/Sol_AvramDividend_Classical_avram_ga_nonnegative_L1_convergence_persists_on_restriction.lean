-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_nonnegative_L1_convergence_persists_on_restriction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:45:55.208669+00:00
-- url     : https://prove2.me/submissions/c1dd2261-6d9c-4e09-9bcc-1aa408e037ea

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (f : ℕ → Ω → ℝ)
    (hI : ∀ m, Integrable (f m) P)
    (hPos : ∀ m ω, 0 ≤ f m ω)
    (hLim : Tendsto (fun m => ∫ ω, f m ω ∂P) atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => ∫ ω in A, f m ω ∂P) atTop (nhds (0 : ℝ))  := by
  have h0 (m : ℕ) : 0 ≤ ∫ ω in A, f m ω ∂P :=
    integral_nonneg (hPos m)
  have hle (m : ℕ) :
      (∫ ω in A, f m ω ∂P) ≤ (∫ ω, f m ω ∂P) := by
    exact integral_mono_measure (Measure.restrict_le_self)
      (Filter.Eventually.of_forall (hPos m)) (hI m)
  exact squeeze_zero h0 hle hLim
