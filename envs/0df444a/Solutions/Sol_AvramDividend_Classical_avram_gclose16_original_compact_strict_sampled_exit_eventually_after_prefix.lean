-- Prove2me | solution 1 for AvramDividend.Classical.avram_gclose16_original_compact_strict_sampled_exit_eventually_after_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T21:47:54.760041+00:00
-- url     : https://prove2.me/submissions/efbe4e5d-2a92-401c-b826-3a85e4ab276f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose15_original_compact_strict_postpayment_uniform_floor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A strictly solvent original compact reserve prefix eventually has no
sampled lower exit at any threshold tending to zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0)
    (hpos : ∀ s : ℝ≥0, s ≤ T →
      0 < x + X.X s ω - rightLimit D s ω)
    (r : ℕ → ℝ≥0) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 (0 : ℝ))) :
    ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤
      (⨅ k : ℕ, if x + X.X (r k) ω - rightLimit D (r k) ω < ε n
        then (r k : WithTop ℝ≥0) else ⊤) := by
  obtain ⟨δ, hδ, hfloor⟩ :=
    avram_gclose15_original_compact_strict_postpayment_uniform_floor
      X x D hD ω T hpos
  have hevent : ∀ᶠ n in atTop, ε n < δ :=
    hε.eventually (Iio_mem_nhds hδ)
  filter_upwards [hevent] with n hn
  refine le_iInf fun k => ?_
  by_cases hbad : x + X.X (r k) ω - rightLimit D (r k) ω < ε n
  · simp only [if_pos hbad]
    have hrk : T ≤ r k := by
      by_contra hnot
      have hklt : r k < T := lt_of_not_ge hnot
      have hbound := hfloor (r k) (le_of_lt hklt)
      linarith
    exact_mod_cast hrk
  · simp only [if_neg hbad]
    exact le_top
