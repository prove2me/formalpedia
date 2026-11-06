-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_inclusive_stopped_three_channel_finite_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:24:59.320046+00:00
-- url     : https://prove2.me/submissions/1d45da2e-9eb7-46d3-8b62-8b600f22d228

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_gaussian_small_large_finite_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Inclusive stopped physical clock preserves all three source quadratic energies. -/
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
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ univ < ⊤)
    (τ : Ω → ℝ≥0) (hτmeas : Measurable τ) :
    let S : Set (ℝ≥0 × Ω) := {p | p.1 ≤ τ p.2}
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    MeasurableSet S ∧
    (∫⁻ p, ENNReal.ofReal
      ((Real.exp (-(q * (p.1 : ℝ))) *
        (X.σ * deriv w (U p))) ^ 2) ∂(μ.restrict S)) < ⊤ ∧
    (∫⁻ p, (∫⁻ z in Ioo (-ε) (0 : ℝ),
      ENNReal.ofReal
        ((Real.exp (-(q * (p.1 : ℝ))) *
          ((w (U p + z) - w (U p)) -
           (w (δ + z) - w δ))) ^ 2) ∂X.ν) ∂(μ.restrict S)) < ⊤ ∧
    (∫⁻ p, (∫⁻ z in Iic (-ε),
      ENNReal.ofReal
        ((Real.exp (-(q * (p.1 : ℝ))) *
           (w (U p + z) - w (U p))) ^ 2) ∂X.ν) ∂(μ.restrict S)) < ⊤ := by
  have hS : MeasurableSet {p : ℝ≥0 × Ω | p.1 ≤ τ p.2} :=
    measurableSet_le measurable_fst (hτmeas.comp measurable_snd)
  have hμr : (μ.restrict {p : ℝ≥0 × Ω | p.1 ≤ τ p.2}) univ < ⊤ := by
    have hle : μ.restrict {p : ℝ≥0 × Ω | p.1 ≤ τ p.2} ≤ μ :=
      Measure.restrict_le_self
    exact lt_of_le_of_lt (hle univ) hμ
  have hE :=
    avram_p4_f3_original_discounted_gaussian_small_large_finite_energy
      X x D w C hw_cont hw_neg hw_smooth q hq δ K ε
      hδ hδK hK hε
      (μ.restrict {p : ℝ≥0 × Ω | p.1 ≤ τ p.2}) hμr
  exact ⟨hS, hE⟩
