-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18q_original_largejump_Campbell_lintegral_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:08:05.835446+00:00
-- url     : https://prove2.me/submissions/49bcbdfe-e56f-4ad5-9e08-59f4a8e717ce

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ja18q1_original_largejump_Campbell_exact_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_ja18q2_original_largejump_pathwise_enorm_bound
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      (∫⁻ ω, ‖avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω‖ₑ ∂P) ≤
        (t : ℝ≥0∞) *
          (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂X.ν) := by
  intro t
  calc
    (∫⁻ ω, ‖avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω‖ₑ ∂P) ≤
        (∫⁻ ω, ∫⁻ p in (Ioc (0 : ℝ≥0) t ×ˢ Iic (-1 : ℝ)),
          ENNReal.ofReal |p.2| ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) := by
              exact lintegral_mono (avram_ja18q2_original_largejump_pathwise_enorm_bound X t)
    _ = (t : ℝ≥0∞) *
        (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂X.ν) :=
          avram_ja18q1_original_largejump_Campbell_exact_nonnegative X t
