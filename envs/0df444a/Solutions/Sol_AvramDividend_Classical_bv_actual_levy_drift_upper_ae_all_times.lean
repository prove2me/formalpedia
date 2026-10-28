-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_levy_drift_upper_ae_all_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:11:15.436007+00:00
-- url     : https://prove2.me/submissions/4b8dc95f-e162-46f0-b70d-2285cd6f331f

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_schedule
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.NNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The entire actual BV Levy path is below the deterministic drift line almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω ≤ (t : ℝ) * X.drift := by
  obtain ⟨ts, hdense⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
  refine (bv_actual_levy_drift_upper_ae_schedule X hBV ts).mono ?_
  intro ω hω t
  obtain ⟨u, _, hu, hu_tendsto⟩ :=
    (show Dense (Set.range ts) from hdense).exists_seq_strictAnti_tendsto t
  have hu_within : Tendsto u atTop (𝓝[Set.Ici t] t) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hu_tendsto, Filter.Eventually.of_forall
        (fun n => Set.mem_Ici.mpr (le_of_lt (hu n).1))⟩
  have hxlim : Tendsto (fun n => X.X (u n) ω) atTop (𝓝 (X.X t ω)) :=
    (show Tendsto (fun s => X.X s ω) (𝓝[Set.Ici t] t)
      (𝓝 (X.X t ω)) from X.rightCont ω t).comp hu_within
  have hdlim : Tendsto (fun n => (u n : ℝ) * X.drift)
      atTop (𝓝 ((t : ℝ) * X.drift)) :=
    ((NNReal.continuous_coe.tendsto t).mul_const X.drift).comp hu_tendsto
  apply le_of_tendsto_of_tendsto hxlim hdlim
  filter_upwards [] with n
  obtain ⟨i, hi⟩ := (hu n).2
  rw [← hi]
  exact hω i
