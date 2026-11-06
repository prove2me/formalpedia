-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_discounted_gaussian_coefficient_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:19:36.280587+00:00
-- url     : https://prove2.me/submissions/3d2c8fe8-b9f1-4335-a573-189240dfd71b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_predividend_clipped_reserve_jointly_measurable_bounded
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original clipped pre-jump discounted Gaussian coefficient is jointly measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q δ K : ℝ) (hδK : δ ≤ K) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    Measurable (fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.σ * deriv w (U p))) := by
  dsimp only
  have hU : Measurable (fun p : ℝ≥0 × Ω =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ) :=
    (avram_p4_f3_original_predividend_clipped_reserve_jointly_measurable_bounded
      X x D hD δ K hδK).1
  have ht : Measurable (fun p : ℝ≥0 × Ω => (p.1 : ℝ)) :=
    measurable_coe_nnreal_real.comp measurable_fst
  have hd : Measurable (fun p : ℝ≥0 × Ω =>
      Real.exp (-(q * (p.1 : ℝ)))) :=
    Real.continuous_exp.measurable.comp ((measurable_const.mul ht).neg)
  exact hd.mul (measurable_const.mul ((measurable_deriv w).comp hU))
