-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_scale_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:52:41.788001+00:00
-- url     : https://prove2.me/submissions/54d19b10-8724-439a-8b8c-6257e5f7639b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scale_exp_lower_growth
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The original positive-discount q-scale function diverges to plus
infinity as the reserve grows, without any positive-axis C1 assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Tendsto W atTop atTop := by
  obtain ⟨φ, hφ, hbound⟩ :=
    avram_wave3_02_scale_exp_lower_growth X hX q hq W hW
  obtain ⟨hWpos, _⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  have hW1 : 0 < W 1 := hWpos 1 (by norm_num)
  have hlin : Tendsto (fun a : ℝ => a * φ) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hφ tendsto_id
  have hshift : Tendsto (fun a : ℝ => a * φ + -φ) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (-φ) hlin
  have hexp : Tendsto (fun a : ℝ => Real.exp (φ * (a - 1)))
      atTop atTop := by
    have heq : (fun a : ℝ => Real.exp (φ * (a - 1))) =
        (fun a : ℝ => Real.exp (a * φ + -φ)) := by
      funext a
      congr 1
      ring
    rw [heq]
    exact Real.tendsto_exp_atTop.comp hshift
  have hbelow : Tendsto (fun a : ℝ =>
      W 1 * Real.exp (φ * (a - 1))) atTop atTop := by
    have ht := Filter.Tendsto.atTop_mul_const hW1 hexp
    simpa only [mul_comm] using ht
  have hle : ∀ᶠ a : ℝ in atTop,
      W 1 * Real.exp (φ * (a - 1)) ≤ W a := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    exact hbound a ha
  exact Filter.tendsto_atTop_mono' atTop hle hbelow
