-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_discounted_gaussian_small_large_finite_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:50:36.564723+00:00
-- url     : https://prove2.me/submissions/f8892320-eda6-4fb1-8f99-a600b7d799f6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_physical_gaussian_finite_joint_energy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_small_large_joint_finite_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Same original stopped three stochastic source channels retain discounted quadratic energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) (hε : 0 < ε)
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ univ < ⊤) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    (∫⁻ p, ENNReal.ofReal
      ((Real.exp (-(q * (p.1 : ℝ))) *
        (X.σ * deriv w (U p))) ^ 2) ∂μ) < ⊤ ∧
    (∫⁻ p, (∫⁻ z in Ioo (-ε) (0 : ℝ),
      ENNReal.ofReal
        ((Real.exp (-(q * (p.1 : ℝ))) *
          ((w (U p + z) - w (U p)) -
           (w (δ + z) - w δ))) ^ 2) ∂X.ν) ∂μ) < ⊤ ∧
    (∫⁻ p, (∫⁻ z in Iic (-ε),
      ENNReal.ofReal
        ((Real.exp (-(q * (p.1 : ℝ))) *
           (w (U p + z) - w (U p))) ^ 2) ∂X.ν) ∂μ) < ⊤ := by
  have hg :=
    avram_p4_f3_original_discounted_physical_gaussian_finite_joint_energy
      X x D w C hw_cont hw_neg hw_smooth q hq δ K ε
      hδ hδK hK hε μ hμ
  have hj :=
    avram_p4_f3_original_discounted_small_large_joint_finite_energy
      X x D w C hw_cont hw_neg hw_smooth q hq δ K ε
      hδ hδK hK hε μ hμ
  exact ⟨hg, hj.1, hj.2⟩
