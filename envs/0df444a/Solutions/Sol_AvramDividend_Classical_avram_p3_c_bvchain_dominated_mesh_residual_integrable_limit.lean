-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_dominated_mesh_residual_integrable_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:28:44.869342+00:00
-- url     : https://prove2.me/submissions/a0dfc0f0-302a-42bb-ab11-e7f07126d1d5

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter

/-- A dominated almost-everywhere BV source-mesh limit is integrable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → Ω → ℝ) (Efinal B : Ω → ℝ)
    (hMeas : ∀ n, AEStronglyMeasurable (E n) P)
    (hB : Integrable B P)
    (hBound : ∀ n, ∀ᵐ ω ∂P, |E n ω| ≤ B ω)
    (hLimit : ∀ᵐ ω ∂P, Tendsto (fun n => E n ω) atTop (nhds (Efinal ω))) :
    Integrable Efinal P := by
  have hM : AEStronglyMeasurable Efinal P :=
    aestronglyMeasurable_of_tendsto_ae atTop hMeas hLimit
  have hAll : ∀ᵐ ω ∂P, ∀ n, |E n ω| ≤ B ω :=
    (ae_all_iff).2 hBound
  apply Integrable.mono hB hM
  filter_upwards [hAll, hLimit] with ω hω hωlim
  have hLimitBound : |Efinal ω| ≤ B ω :=
    le_of_tendsto hωlim.abs (Filter.Eventually.of_forall hω)
  simpa only [Real.norm_eq_abs] using
    (hLimitBound.trans (le_abs_self (B ω)))
