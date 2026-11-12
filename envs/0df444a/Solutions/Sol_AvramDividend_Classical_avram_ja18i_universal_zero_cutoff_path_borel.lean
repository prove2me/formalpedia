-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18i_universal_zero_cutoff_path_borel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:28:53.447386+00:00
-- url     : https://prove2.me/submissions/d21a31e2-0a46-4dbf-95da-8d12fc0fdac7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_generic_negative_mark_window_integral_formula
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A universal measurable functional extracts the cutoff-zero residual
from the original càdlàg path without changing the probability space. -/
theorem solution
    (c : ℝ) (t : ℝ≥0) :
    ∃ W : (ℝ≥0 → ℝ) → ℝ, Measurable W ∧
      ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
        {𝓕 : Filtration ℝ≥0 mΩ}
        (X : SpectrallyNegativeLevy P 𝓕) (hc : X.c = c) (ω : Ω),
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω =
          W (fun u : ℝ≥0 => X.X u ω) := by
  classical
  let B : Set ℝ := Iic (-1 : ℝ)
  let g : ℝ → ℝ≥0∞ := fun z =>
    if z ∈ B then ENNReal.ofReal (-z) else 0
  have hg : Measurable g := by
    dsimp [g]
    exact Measurable.ite measurableSet_Iic (by fun_prop) measurable_const
  obtain ⟨J, hJ, hJpath⟩ :=
    avram_bv_jump8_cadlag_mark_weight_lintegral_borel t g hg
  let W : (ℝ≥0 → ℝ) → ℝ := fun Y =>
    Y t - (t : ℝ) * c + (J Y).toReal
  have hW : Measurable W :=
    ((measurable_pi_apply t).sub_const ((t : ℝ) * c)).add
      (ENNReal.measurable_toReal.comp hJ)
  refine ⟨W, hW, ?_⟩
  intro Ω mΩ P 𝓕 X hc ω
  let Y : ℝ≥0 → ℝ := fun u => X.X u ω
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
      (fun u : ℝ≥0 => (u, Y u - Function.leftLim Y u))
  have hNeg : ∀ z ∈ B, z ≤ 0 := by
    intro z hz
    exact hz.trans (by norm_num)
  have hJformula := hJpath Y (X.rightCont ω) (X.leftLim ω)
  have hSign := avram_mix_gauss14_generic_negative_mark_window_integral_formula
    μ (0 : ℝ≥0) t B measurableSet_Iic hNeg
  have hLarge : avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω =
      -((J Y).toReal) := by
    change (∫ p in (Ioc 0 t ×ˢ B), p.2 ∂μ) = -((J Y).toReal)
    rw [hSign, hJformula]
  have hSmall : avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω = 0 := by
    simp [avram_p4_h_gaussian_intrinsic_small_band_compensated]
  change X.X t ω - (t : ℝ) * X.c -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω -
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω =
      Y t - (t : ℝ) * c + (J Y).toReal
  rw [hSmall, hLarge, hc]
  ring
