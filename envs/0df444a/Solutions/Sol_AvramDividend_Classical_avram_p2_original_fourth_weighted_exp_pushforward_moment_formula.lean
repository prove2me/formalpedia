-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_fourth_weighted_exp_pushforward_moment_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:02:04.391798+00:00
-- url     : https://prove2.me/submissions/7f2aaee8-136e-44c8-b67c-dacfb033a50e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Polynomial moments of the actual original fourth-weighted exponential
pushforward are exactly source-weighted moments on the same sample space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (k : ℕ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      ((P.withDensity (fun ω => ENNReal.ofReal
        ((Real.exp (X.X t ω) - 1) ^ 4))).map
        (fun ω => Real.exp (X.X t ω)))) =
    (∫⁻ ω, ENNReal.ofReal ((Real.exp (X.X t ω) - 1) ^ 4) *
      ENNReal.ofReal ((Real.exp (X.X t ω)) ^ k) ∂P) := by
  have hXm : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hG : Measurable (fun ω : Ω => Real.exp (X.X t ω)) :=
    Real.measurable_exp.comp hXm
  have hW : Measurable (fun ω : Ω =>
      ENNReal.ofReal ((Real.exp (X.X t ω) - 1) ^ 4)) :=
    ENNReal.measurable_ofReal.comp ((hG.sub_const 1).pow_const 4)
  have hF : Measurable (fun z : ℝ => ENNReal.ofReal (z ^ k)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const k)
  calc
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      ((P.withDensity (fun ω => ENNReal.ofReal
        ((Real.exp (X.X t ω) - 1) ^ 4))).map
        (fun ω => Real.exp (X.X t ω)))) =
      ∫⁻ ω, ENNReal.ofReal ((Real.exp (X.X t ω)) ^ k) ∂
        (P.withDensity (fun ω => ENNReal.ofReal
          ((Real.exp (X.X t ω) - 1) ^ 4))) := by
      exact lintegral_map hF hG
    _ = ∫⁻ ω, ENNReal.ofReal ((Real.exp (X.X t ω) - 1) ^ 4) *
        ENNReal.ofReal ((Real.exp (X.X t ω)) ^ k) ∂P := by
      simpa only [Pi.mul_apply, Function.comp_apply] using
        (lintegral_withDensity_eq_lintegral_mul P hW (hF.comp hG))
