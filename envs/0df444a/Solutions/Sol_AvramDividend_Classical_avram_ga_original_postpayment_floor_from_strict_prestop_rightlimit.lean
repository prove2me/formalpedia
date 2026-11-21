-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_postpayment_floor_from_strict_prestop_rightlimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:46:38.595176+00:00
-- url     : https://prove2.me/submissions/f4ae2697-49fe-4933-b1c3-66621f422b10

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Filter Topology Set MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (t ρ : ℝ≥0) (δ : ℝ) (ht : t < ρ)
    (hRight : Tendsto
      (fun u : ℝ≥0 => riskProcess X x D u ω)
      (𝓝[>] t) (𝓝 (x + X.X t ω - rightLimit D t ω)))
    (hFloor : ∀ u : ℝ≥0, 0 < u → u < ρ →
      δ ≤ riskProcess X x D u ω) :
    δ ≤ x + X.X t ω - rightLimit D t ω := by
  apply ge_of_tendsto hRight
  have hafter : ∀ᶠ u in 𝓝[>] t, t < u := self_mem_nhdsWithin
  have hbefore : ∀ᶠ u in 𝓝[>] t, u < ρ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (isOpen_Iio.mem_nhds ht)
  filter_upwards [hafter, hbefore] with u hu hv
  exact hFloor u (lt_of_le_of_lt (show (0 : ℝ≥0) ≤ t from zero_le) hu) hv
