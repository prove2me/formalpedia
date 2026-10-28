-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_levy_residual_ae_monotone_all_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:26:21.056881+00:00
-- url     : https://prove2.me/submissions/9466c83a-79fc-4936-bca1-f1afd206cd8f

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_increment_ae_schedule_pairs
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The residual of the actual BV Levy process is nondecreasing almost surely on all real times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      Monotone (fun t : ℝ≥0 => (t : ℝ) * X.drift - X.X t ω) := by
  obtain ⟨ts, hdense⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
  refine (bv_actual_levy_drift_increment_ae_schedule_pairs X hBV ts).mono ?_
  intro ω hω s t hst
  rcases eq_or_lt_of_le hst with heq | hlt
  · subst t
    exact le_rfl
  obtain ⟨u, _, hu, hsu⟩ :=
    (show Dense (Set.range ts) from hdense).exists_seq_strictAnti_tendsto_of_lt hlt
  obtain ⟨v, _, hv, htv⟩ :=
    (show Dense (Set.range ts) from hdense).exists_seq_strictAnti_tendsto t
  have hus : Tendsto u atTop (𝓝[Set.Ici s] s) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hsu, Filter.Eventually.of_forall
        (fun n => Set.mem_Ici.mpr (le_of_lt (hu n).1.1))⟩
  have hvt : Tendsto v atTop (𝓝[Set.Ici t] t) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨htv, Filter.Eventually.of_forall
        (fun n => Set.mem_Ici.mpr (le_of_lt (hv n).1))⟩
  have hsX : Tendsto (fun n => X.X (u n) ω) atTop (𝓝 (X.X s ω)) :=
    (show Tendsto (fun x => X.X x ω) (𝓝[Set.Ici s] s)
      (𝓝 (X.X s ω)) from X.rightCont ω s).comp hus
  have htX : Tendsto (fun n => X.X (v n) ω) atTop (𝓝 (X.X t ω)) :=
    (show Tendsto (fun x => X.X x ω) (𝓝[Set.Ici t] t)
      (𝓝 (X.X t ω)) from X.rightCont ω t).comp hvt
  have hsD : Tendsto (fun n => (u n : ℝ) * X.drift)
      atTop (𝓝 ((s : ℝ) * X.drift)) :=
    ((NNReal.continuous_coe.tendsto s).mul_const X.drift).comp hsu
  have htD : Tendsto (fun n => (v n : ℝ) * X.drift)
      atTop (𝓝 ((t : ℝ) * X.drift)) :=
    ((NNReal.continuous_coe.tendsto t).mul_const X.drift).comp htv
  have hsY := hsD.sub hsX
  have htY := htD.sub htX
  apply le_of_tendsto_of_tendsto hsY htY
  filter_upwards [] with n
  obtain ⟨i, hi⟩ := (hu n).2
  obtain ⟨j, hj⟩ := (hv n).2
  have hij : ts i ≤ ts j := by
    rw [hi, hj]
    exact le_of_lt ((hu n).1.2.trans (hv n).1)
  have hinc := hω i j hij
  have hcoe : ((ts j - ts i : ℝ≥0) : ℝ) =
      (ts j : ℝ) - (ts i : ℝ) := NNReal.coe_sub hij
  rw [hcoe, hi, hj] at hinc
  linarith
