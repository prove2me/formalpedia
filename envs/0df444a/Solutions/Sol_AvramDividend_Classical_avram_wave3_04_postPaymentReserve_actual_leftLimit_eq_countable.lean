-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_postPaymentReserve_actual_leftLimit_eq_countable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:26:23.928934+00:00
-- url     : https://prove2.me/submissions/eb32f163-38c0-40d7-b2b8-a25008aa81c3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_prejump_upper

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The explicit past-time countable limit equals the genuine left limit
of the same controlled spectrally negative Levy process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    ∃ l : ℝ,
      Tendsto (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
        (𝓝[<] t) (𝓝 l) ∧
      Filter.limUnder atTop
        (fun n : ℕ =>
          x + X.X (t - t / ((n : ℝ≥0) + 2)) ω -
            rightLimit D (t - t / ((n : ℝ≥0) + 2)) ω) = l := by
  obtain ⟨l, hl, _⟩ :=
    avram_wave3_04_postPaymentReserve_prejump_upper X x D hD ω t ht
  refine ⟨l, hl, ?_⟩
  have hdiv : Tendsto
      (fun n : ℕ => t / ((n : ℝ≥0) + 2))
      atTop (𝓝 0) := by
    convert (tendsto_add_atTop_iff_nat 2).2
        (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ≥0) t) using 1
    ext n
    norm_num [Nat.cast_add]
  have hlim : Tendsto
      (fun n : ℕ => t - t / ((n : ℝ≥0) + 2))
      atTop (𝓝 t) := by
    have hc : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
    simpa only [tsub_zero] using hc.sub hdiv
  have hclock : Tendsto
      (fun n : ℕ => t - t / ((n : ℝ≥0) + 2))
      atTop (𝓝[<] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hlim, ?_⟩
    exact Filter.Eventually.of_forall fun n => by
      have hp : 0 < t / ((n : ℝ≥0) + 2) := by positivity
      exact tsub_lt_self ht hp
  exact (hl.comp hclock).limUnder_eq
