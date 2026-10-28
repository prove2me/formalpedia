-- Prove2me | solution 1 for AvramDividend.Classical.bv_ae_cauchy_plus_in_measure_bundle_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:04:33.823867+00:00
-- url     : https://prove2.me/submissions/397d34b0-5221-4c74-b6b0-388e06fa1ea9

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.UniformSpace.Cauchy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Topology

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : ℕ → Ω → ℝ)
    (hC : ∀ᵐ ω ∂P, CauchySeq (fun n => f n ω))
    (hProb : TendstoInMeasure P f atTop (fun _ => (0 : ℝ))) :
    ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 0) := by
  obtain ⟨ns, hns, hsub⟩ := hProb.exists_seq_tendsto_ae
  filter_upwards [hC, hsub] with ω hCω hsubω
  have hnsTends : Tendsto ns atTop atTop := hns.tendsto_atTop
  exact tendsto_nhds_of_cauchySeq_of_subseq
    hCω hnsTends (by simpa only [Function.comp_def] using hsubω)
