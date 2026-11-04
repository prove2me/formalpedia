-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_negative_halfline_expected_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:49:51.26426+00:00
-- url     : https://prove2.me/submissions/2974a926-07f9-4dcb-b21e-c849af6bc219

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_separated_band_finite_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Turn the proved original separated-band finite mean into a finite linear
horizon bound, with a constant allowed to depend on the fixed horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-ε)) ∂P) ≤ ENNReal.ofReal (C * (T : ℝ)) := by
  classical
  let M : ℝ≥0∞ :=
    ∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-ε)) ∂P
  have hM : M < ⊤ := by
    simpa only [M] using
      (avram_p2_c_borel_original_separated_band_finite_mean X T hT ε hε)
  have ht : 0 < (T : ℝ) := NNReal.coe_pos.mpr hT
  let C : ℝ := (M.toReal + 1) / (T : ℝ)
  have hC : 0 < C := by
    dsimp [C]
    apply div_pos _ ht
    have hNonneg : 0 ≤ M.toReal := ENNReal.toReal_nonneg
    linarith
  refine ⟨C, hC, ?_⟩
  change M ≤ ENNReal.ofReal (C * (T : ℝ))
  have hCT : C * (T : ℝ) = M.toReal + 1 := by
    dsimp [C]
    exact div_mul_cancel₀ _ (ne_of_gt ht)
  rw [hCT]
  calc
    M = ENNReal.ofReal M.toReal :=
      (ENNReal.ofReal_toReal (ne_of_lt hM)).symm
    _ ≤ ENNReal.ofReal (M.toReal + 1) :=
      ENNReal.ofReal_le_ofReal (by linarith)
