-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_vector_common_law_limit_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:01:05.51995+00:00
-- url     : https://prove2.me/submissions/8dc8f015-f476-49f5-9854-8a24c53a9c98

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Topology

theorem solution
    {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] [HasOuterApproxClosed E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → E) (Z Z₀ : Ω → E)
    (hY : ∀ n, AEMeasurable (Y n) P)
    (hZ : AEMeasurable Z P)
    (hZ₀ : AEMeasurable Z₀ P)
    (hLaw : ∀ n, Measure.map (Y n) P = Measure.map Z₀ P)
    (hLim : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω))) :
    Measure.map Z P = Measure.map Z₀ P := by
  have hLimitZ :
      TendstoInDistribution Y atTop Z (fun _ => P) P :=
    tendstoInDistribution_of_ae_tendsto hY hZ hLim
  have hIdent : ∀ n,
      ProbabilityTheory.IdentDistrib (Y 0) (Y n) P P := by
    intro n
    exact ⟨hY 0, hY n, (hLaw 0).trans (hLaw n).symm⟩
  have hAnchor : ProbabilityTheory.IdentDistrib (Y 0) Z₀ P P :=
    ⟨hY 0, hZ₀, hLaw 0⟩
  have hLimitZ₀ :
      TendstoInDistribution Y atTop Z₀ (fun _ => P) P :=
    tendstoInDistribution_of_identDistrib 0 hIdent hAnchor
  exact tendstoInDistribution_unique Y hLimitZ hLimitZ₀
