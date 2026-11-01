-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_original_record_factor_tendsto_one_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:23:14.221492+00:00
-- url     : https://prove2.me/submissions/c522a05a-2f82-4393-a0e1-f936272b5384

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_unbounded_genuine_record_scale_sandwich

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
/-- Original reflected first-record discount tends to one as height falls
to zero, by the genuine q-scale sandwich without a standing hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun h : ℝ =>
      ∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ≥0∞)) := by
  let F : ℝ → ℝ≥0∞ := fun h =>
    ∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hjump
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv a ha
  have hWcont : ContinuousAt W a := scaleFunction_continuousAt_away_zero X q W hW a (ne_of_gt ha)
  have hWminus : ContinuousAt (fun h : ℝ => W (a - h)) 0 := by
    have hp : ContinuousAt (fun h : ℝ => a - h) 0 := by fun_prop
    have hc : ContinuousAt W (a - (0 : ℝ)) := by simpa using hWcont
    change ContinuousAt (W ∘ fun h : ℝ => a - h) 0
    exact hc.comp hp
  have hWplus : ContinuousAt (fun h : ℝ => W (a + h)) 0 := by
    have hp : ContinuousAt (fun h : ℝ => a + h) 0 := by fun_prop
    have hc : ContinuousAt W (a + (0 : ℝ)) := by simpa using hWcont
    change ContinuousAt (W ∘ fun h : ℝ => a + h) 0
    exact hc.comp hp
  have hLcont : ContinuousAt (fun h : ℝ => W (a - h) / W a) 0 :=
    hWminus.div continuousAt_const (ne_of_gt hWa)
  have hUcont : ContinuousAt (fun h : ℝ => W a / W (a + h)) 0 :=
    continuousAt_const.div hWplus (by simpa using ne_of_gt hWa)
  have hLlim : Tendsto (fun h : ℝ =>
      ENNReal.ofReal (W (a - h) / W a)) (𝓝[>] (0 : ℝ))
      (𝓝 (1 : ℝ≥0∞)) := by
    have hc := ENNReal.continuous_ofReal.continuousAt.comp hLcont
    have ht : Tendsto (fun h : ℝ => ENNReal.ofReal (W (a - h) / W a))
        (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ≥0∞)) := by
      simpa only [Function.comp_def, sub_zero, div_self (ne_of_gt hWa),
        ENNReal.ofReal_one] using hc.tendsto
    exact ht.mono_left (inf_le_left : (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ))
  have hUlim : Tendsto (fun h : ℝ =>
      ENNReal.ofReal (W a / W (a + h))) (𝓝[>] (0 : ℝ))
      (𝓝 (1 : ℝ≥0∞)) := by
    have hc := ENNReal.continuous_ofReal.continuousAt.comp hUcont
    have ht : Tendsto (fun h : ℝ => ENNReal.ofReal (W a / W (a + h)))
        (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ≥0∞)) := by
      simpa only [Function.comp_def, add_zero, div_self (ne_of_gt hWa),
        ENNReal.ofReal_one] using hc.tendsto
    exact ht.mono_left (inf_le_left : (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ))
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), 0 < h := by
    have hmem : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
        h ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
    exact hmem
  have hlt : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < a :=
    Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds ha)
  have hlo : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (W (a - h) / W a) ≤ F h := by
    filter_upwards [hpos, hlt] with h hh hha
    exact (avram_wave3_01_unbounded_genuine_record_scale_sandwich
      X q hq W hW hnbv a h ha hh hha).1
  have hhi : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      F h ≤ ENNReal.ofReal (W a / W (a + h)) := by
    filter_upwards [hpos, hlt] with h hh hha
    exact (avram_wave3_01_unbounded_genuine_record_scale_sandwich
      X q hq W hW hnbv a h ha hh hha).2
  exact Filter.Tendsto.squeeze' hLlim hUlim hlo hhi
