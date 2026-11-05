-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_preexit_left_limit_closed_band_bound_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:54:15.391204+00:00
-- url     : https://prove2.me/submissions/79197d42-1fbe-4951-b709-88a8da951e08

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (lower upper : ℝ) (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hstay : ∀ s : ℝ≥0, s < t →
      lower ≤ x + X.X s ω - rightLimit D s ω ∧
        x + X.X s ω - rightLimit D s ω ≤ upper) :
    ∃ l : ℝ,
      Tendsto (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
        (𝓝[<] t) (𝓝 l) ∧
      (lower ≤ l ∧ l ≤ upper) ∧
      (0 < l ∧ ENNReal.ofReal l < C) ∧
      ContDiffWithinAt ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} l := by
  obtain ⟨l, hlim⟩ :=
    (postPaymentReserve_cadlag_adapted X x D hD).2.1 ω t ht
  have hband : ∀ᶠ s : ℝ≥0 in 𝓝[<] t,
      x + X.X s ω - rightLimit D s ω ∈ Set.Icc lower upper := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hstay s hs
  haveI : NeBot (𝓝[<] t) :=
    nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hlband : l ∈ Set.Icc lower upper :=
    isClosed_Icc.mem_of_tendsto hlim hband
  have hpos : 0 < l := lt_of_lt_of_le hlower hlband.1
  have hlcap : ENNReal.ofReal l < C := hcap l hlband
  exact ⟨l, hlim, hlband, ⟨hpos, hlcap⟩, hw l ⟨hpos, hlcap⟩⟩
