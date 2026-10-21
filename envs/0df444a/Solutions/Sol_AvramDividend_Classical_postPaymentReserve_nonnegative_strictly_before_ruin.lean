-- Prove2me | solution 1 for AvramDividend.Classical.postPaymentReserve_nonnegative_strictly_before_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:18:45.91299+00:00
-- url     : https://prove2.me/submissions/48854b5d-87db-4108-b25d-fa47be9e36b6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_tendsto_postPaymentReserve_right

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ x + X.X t ω - rightLimit D t ω := by
  by_contra hn
  have hneg : x + X.X t ω - rightLimit D t ω < 0 :=
    lt_of_not_ge hn
  haveI : NeBot (𝓝[>] t) :=
    nhdsGT_neBot_of_exists_gt
      ⟨t + 1, lt_add_of_pos_right t zero_lt_one⟩
  have hfuture : ∀ᶠ s in 𝓝[>] t,
      riskProcess X x D s ω < 0 :=
    (riskProcess_tendsto_postPaymentReserve_right
      X x D hD ω t).eventually (isOpen_Iio.mem_nhds hneg)
  have hcast :
      Tendsto (fun s : ℝ≥0 => (s : ℝ≥0∞))
        (𝓝[>] t) (𝓝 (t : ℝ≥0∞)) :=
    (ENNReal.continuous_coe.tendsto t).mono_left nhdsWithin_le_nhds
  have hbelow : Filter.Eventually
      (fun s : ℝ≥0 => (s : ℝ≥0∞) < ruinTime X x D ω)
      (𝓝[>] t) :=
    hcast.eventually (Iio_mem_nhds ht)
  obtain ⟨s, hsneg, hslt⟩ := (hfuture.and hbelow).exists
  have hle : ruinTime X x D ω ≤ (s : ℝ≥0∞) := by
    unfold ruinTime
    exact iInf_le_of_le s (iInf_le _ hsneg)
  exact (not_lt_of_ge hle) hslt
