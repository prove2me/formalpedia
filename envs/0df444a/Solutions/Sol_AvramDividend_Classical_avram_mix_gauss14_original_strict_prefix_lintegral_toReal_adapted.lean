-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_gauss14_original_strict_prefix_lintegral_toReal_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:10:56.417214+00:00
-- url     : https://prove2.me/submissions/abd43aab-2ea2-4143-b94d-85f89b263be0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_arbitrary_prefix_laplace_filtration_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Original-prefix real marked jump mass adaptedness, by an explicit functional logarithm identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (k : ℕ) :
    Measurable[𝓕 T] (fun ω : Ω =>
      ((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
        then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) := by
  let J : Ω → ℝ := fun ω =>
    ((∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then ENNReal.ofReal (-p.2) else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)
  change Measurable[𝓕 T] J
  have hExp : Measurable[𝓕 T] (fun ω => Real.exp (-(J ω))) := by
    exact avram_route_runner_f_original_arbitrary_prefix_laplace_filtration_measurable X T k
  have hLog : Measurable[𝓕 T]
      (Real.log ∘ fun ω => Real.exp (-(J ω))) :=
    Real.measurable_log.comp hExp
  have hNeg : Measurable[𝓕 T]
      (-(Real.log ∘ fun ω => Real.exp (-(J ω)))) := hLog.neg
  have hfun : (-(Real.log ∘ fun ω : Ω => Real.exp (-(J ω)))) = J := by
    funext ω
    change -Real.log (Real.exp (-(J ω))) = J ω
    simp
  rw [hfun] at hNeg
  exact hNeg
