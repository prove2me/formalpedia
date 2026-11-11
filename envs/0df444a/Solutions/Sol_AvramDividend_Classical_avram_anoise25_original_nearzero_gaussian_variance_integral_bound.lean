-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise25_original_nearzero_gaussian_variance_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T09:21:58.784104+00:00
-- url     : https://prove2.me/submissions/0ad7873d-0339-4fe7-8136-49a5485aea49

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Genuine finite-intensity near-zero mark variance is bounded quadratically. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (n : ℕ) :
    let ε : ℝ := 1 / ((n : ℝ) + 1)
    0 ≤ (∫ z in Ioo (-ε) 0, z ^ 2 ∂X.ν) ∧
      (∫ z in Ioo (-ε) 0, z ^ 2 ∂X.ν) ≤
        ε ^ 2 * (X.ν (Iio (0 : ℝ))).toReal := by
  intro ε
  let S : Set ℝ := Ioo (-ε) 0
  have hε0 : 0 ≤ ε := by dsimp [ε]; positivity
  have hSet : S ⊆ Iio (0 : ℝ) := by
    intro z hz
    exact hz.2
  have hMeasS : MeasurableSet S := measurableSet_Ioo
  have hNuLe : X.ν S ≤ X.ν (Iio (0 : ℝ)) := measure_mono hSet
  have hNuFin : X.ν S ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hNuLe (lt_top_iff_ne_top.mpr hFinite))
  have hMark (z : ℝ) (hz : z ∈ S) : z ^ 2 ≤ ε ^ 2 := by
    have hzLower : -ε < z := hz.1
    have hzUpper : z < 0 := hz.2
    have hm : 0 ≤ (ε + z) * (ε - z) :=
      mul_nonneg (by linarith [hzLower]) (by linarith [hzUpper, hε0])
    nlinarith [hm]
  have hLin :
      (∫⁻ z in S, ENNReal.ofReal (z ^ 2) ∂X.ν) ≤
        ENNReal.ofReal (ε ^ 2) * X.ν S := by
    calc
      (∫⁻ z in S, ENNReal.ofReal (z ^ 2) ∂X.ν) ≤
          ∫⁻ z in S, ENNReal.ofReal (ε ^ 2) ∂X.ν := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hMeasS] with z hz
        exact ENNReal.ofReal_le_ofReal (hMark z hz)
      _ = ENNReal.ofReal (ε ^ 2) * X.ν S := by simp [lintegral_const, S]
  have hMassFinite : ENNReal.ofReal (ε ^ 2) * X.ν S ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hNuFin
  have hIeq :
      (∫ z in S, z ^ 2 ∂X.ν) =
        (∫⁻ z in S, ENNReal.ofReal (z ^ 2) ∂X.ν).toReal := by
    exact integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun z => sq_nonneg z))
      (measurable_id.pow_const 2).aestronglyMeasurable
  have hI0 : 0 ≤ (∫ z in S, z ^ 2 ∂X.ν) := by
    rw [hIeq]
    exact ENNReal.toReal_nonneg
  constructor
  · simpa only [S] using hI0
  · change (∫ z in S, z ^ 2 ∂X.ν) ≤ ε ^ 2 * (X.ν (Iio (0 : ℝ))).toReal
    calc
      (∫ z in S, z ^ 2 ∂X.ν) =
          (∫⁻ z in S, ENNReal.ofReal (z ^ 2) ∂X.ν).toReal := hIeq
      _ ≤ (ENNReal.ofReal (ε ^ 2) * X.ν S).toReal :=
        ENNReal.toReal_mono hMassFinite hLin
      _ = ε ^ 2 * (X.ν S).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg ε)]
      _ ≤ ε ^ 2 * (X.ν (Iio (0 : ℝ))).toReal :=
        mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hFinite hNuLe) (sq_nonneg ε)