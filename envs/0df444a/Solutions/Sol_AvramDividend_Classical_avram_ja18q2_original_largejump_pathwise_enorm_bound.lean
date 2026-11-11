-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18q2_original_largejump_pathwise_enorm_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:07:52.904035+00:00
-- url     : https://prove2.me/submissions/117c7666-2466-493c-88b9-0fede89b01d6

import Mathlib
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
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ (t : ℝ≥0) (ω : Ω),
      ‖avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω‖ₑ ≤
        (∫⁻ p in (Ioc (0 : ℝ≥0) t ×ˢ Iic (-1 : ℝ)),
          ENNReal.ofReal |p.2| ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by
  intro t ω
  unfold avram_p4_h_gaussian_intrinsic_large_jump_sum
  simpa only [Real.enorm_eq_ofReal_abs] using
    (enorm_integral_le_lintegral_enorm
      (f := fun p : ℝ≥0 × ℝ => p.2)
      (μ := (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))).restrict
        (Ioc (0 : ℝ≥0) t ×ˢ Iic (-1 : ℝ)))))
