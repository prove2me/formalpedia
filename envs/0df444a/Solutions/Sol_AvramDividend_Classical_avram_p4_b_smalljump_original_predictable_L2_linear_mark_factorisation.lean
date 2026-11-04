-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_L2_linear_mark_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:10:44.109196+00:00
-- url     : https://prove2.me/submissions/11ed05fa-db56-4769-a337-07f07d0959b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact deterministic compensator-side L2 factorisation for an
original-source predictable linear mark with only an L2 coefficient. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤)
    (B : Set ℝ)
    (hBmoment : (∫⁻ z in B,
      ENNReal.ofReal (z^2) ∂X.ν) < ⊤) :
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B, ENNReal.ofReal ((g p * z)^2) ∂X.ν ∂μ) = (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((g p)^2) ∂μ) * (∫⁻ z in B, ENNReal.ofReal (z^2) ∂X.ν) ∧
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B, ENNReal.ofReal ((g p * z)^2) ∂X.ν ∂μ) < ⊤ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hinner (p : ℝ≥0 × Ω) :
      (∫⁻ z in B, ENNReal.ofReal ((g p * z)^2) ∂X.ν) =
        ENNReal.ofReal ((g p)^2) * (∫⁻ z in B, ENNReal.ofReal (z^2) ∂X.ν) := by
    have hf :
        (fun z : ℝ => ENNReal.ofReal ((g p * z)^2)) =
          (fun z : ℝ => ENNReal.ofReal ((g p)^2) *
            ENNReal.ofReal (z^2)) := by
      funext z
      rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg (g p))]
    rw [hf]
    exact lintegral_const_mul _ (by fun_prop)
  have hfactor : (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B, ENNReal.ofReal ((g p * z)^2) ∂X.ν ∂μ) = (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((g p)^2) ∂μ) * (∫⁻ z in B, ENNReal.ofReal (z^2) ∂X.ν) := by
    calc
      (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B, ENNReal.ofReal ((g p * z)^2) ∂X.ν ∂μ) =
          ∫⁻ p : ℝ≥0 × Ω,
            ENNReal.ofReal ((g p)^2) * (∫⁻ z in B, ENNReal.ofReal (z^2) ∂X.ν) ∂μ := by
              apply lintegral_congr_ae
              filter_upwards [] with p
              exact hinner p
      _ = _ := lintegral_mul_const _ (by fun_prop)
  constructor
  · exact hfactor
  · rw [hfactor]
    exact ENNReal.mul_lt_top hgL2 hBmoment
