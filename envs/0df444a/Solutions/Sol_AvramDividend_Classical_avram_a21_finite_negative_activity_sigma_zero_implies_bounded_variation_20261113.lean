-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_finite_negative_activity_sigma_zero_implies_bounded_variation_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:42:28.392639+00:00
-- url     : https://prove2.me/submissions/8de84d1e-6702-4d3b-b850-970151b15ac8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Finite negative Levy activity and no Gaussian term imply bounded variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hσ : X.σ = 0) :
    X.BoundedVariation := by
  change X.σ = 0 ∧
    (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) < ⊤
  constructor
  · exact hσ
  · have hSub : Ioo (-1 : ℝ) 0 ⊆ Iio (0 : ℝ) := by
      intro z hz
      exact hz.2
    have hM : X.ν (Ioo (-1 : ℝ) 0) ≠ ⊤ := by
      apply ne_of_lt
      exact (measure_mono hSub).trans_lt (lt_top_iff_ne_top.mpr hFinite)
    refine setLIntegral_lt_top_of_le_nnreal hM ⟨1, ?_⟩
    intro z hz
    have hzLow : (-1 : ℝ) < z := hz.1
    have hzUp : z < (0 : ℝ) := hz.2
    have hAbs : |z| ≤ (1 : ℝ) := by
      rw [abs_of_neg hzUp]
      linarith
    calc
      ENNReal.ofReal |z| ≤ ENNReal.ofReal (1 : ℝ) :=
        ENNReal.ofReal_le_ofReal hAbs
      _ = (1 : ℝ≥0) := by norm_num
