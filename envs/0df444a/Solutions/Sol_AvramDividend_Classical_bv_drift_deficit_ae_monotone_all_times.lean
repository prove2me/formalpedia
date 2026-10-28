-- Prove2me | solution 1 for AvramDividend.Classical.bv_drift_deficit_ae_monotone_all_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:43:19.722772+00:00
-- url     : https://prove2.me/submissions/8e24fcd3-0775-45b7-835c-f3f55b2d84dd

import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_on_countable_schedule
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.NNReal.Lemmas
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Dense scheduled increments and right continuity give genuine BV subordinator paths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      Monotone (fun t : ℝ≥0 => X.drift * (t : ℝ) - X.X t ω) := by
  obtain ⟨ts, hdense⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
  refine (bv_drift_deficit_ae_monotone_on_countable_schedule X hBV ts).mono ?_
  intro ω hω s t hst
  rcases eq_or_lt_of_le hst with heq | hlt
  · subst t
    exact le_rfl
  obtain ⟨u, _, hu, hu_tendsto⟩ :=
    (show Dense (Set.range ts) from hdense).exists_seq_strictAnti_tendsto s
  obtain ⟨v, _, hv, hv_tendsto⟩ :=
    (show Dense (Set.range ts) from hdense).exists_seq_strictAnti_tendsto t
  have hOrder : ∀ᶠ n : ℕ in atTop, u n ≤ v n :=
    (hu_tendsto.eventually_lt hv_tendsto hlt).mono
      (fun n h => le_of_lt h)
  have huWithin : Tendsto u atTop (𝓝[Set.Ici s] s) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hu_tendsto, Filter.Eventually.of_forall
        (fun n => Set.mem_Ici.mpr (le_of_lt (hu n).1))⟩
  have hvWithin : Tendsto v atTop (𝓝[Set.Ici t] t) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hv_tendsto, Filter.Eventually.of_forall
        (fun n => Set.mem_Ici.mpr (le_of_lt (hv n).1))⟩
  have hxU : Tendsto (fun n => X.X (u n) ω)
      atTop (𝓝 (X.X s ω)) :=
    Filter.Tendsto.comp (X.rightCont ω s) huWithin
  have hxV : Tendsto (fun n => X.X (v n) ω)
      atTop (𝓝 (X.X t ω)) :=
    Filter.Tendsto.comp (X.rightCont ω t) hvWithin
  have hdU : Tendsto (fun n => X.drift * (u n : ℝ))
      atTop (𝓝 (X.drift * (s : ℝ))) :=
    tendsto_const_nhds.mul
      ((NNReal.continuous_coe.tendsto s).comp hu_tendsto)
  have hdV : Tendsto (fun n => X.drift * (v n : ℝ))
      atTop (𝓝 (X.drift * (t : ℝ))) :=
    tendsto_const_nhds.mul
      ((NNReal.continuous_coe.tendsto t).comp hv_tendsto)
  apply le_of_tendsto_of_tendsto (hdU.sub hxU) (hdV.sub hxV)
  filter_upwards [hOrder] with n hOrdered
  obtain ⟨i, hi⟩ := (hu n).2
  obtain ⟨j, hj⟩ := (hv n).2
  have hij : ts i ≤ ts j := by
    simpa only [hi, hj] using hOrdered
  rw [← hi, ← hj]
  exact hω i j hij
