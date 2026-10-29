-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_upperray_weighted_exp_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:07:16.283784+00:00
-- url     : https://prove2.me/submissions/fe2d58e9-9688-43e8-9aa8-46410939b485

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The upper-ray factorisation for one nonnegative test gives its exponentially
weighted transform; no full stochastic independence is assumed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    (S : Ω → ℝ) (W : Ω → ENNReal) (β : ℝ)
    (hS : Measurable S) (hW : Measurable W) (hβ : 0 < β)
    (hK : (∫⁻ z, W z ∂μ) ≠ ⊤)
    (hTail : ∀ b : ℝ,
      (μ.withDensity W) {z : Ω | b < S z} =
        μ {z : Ω | b < S z} * (∫⁻ z, W z ∂μ)) :
    (∫⁻ z, W z * ENNReal.ofReal (Real.exp (β * S z)) ∂μ) =
      (∫⁻ z, ENNReal.ofReal (Real.exp (β * S z)) ∂μ) *
        (∫⁻ z, W z ∂μ) := by
  let ν : Measure Ω := μ.withDensity W
  let f : Ω → ℝ := fun z => Real.exp (β * S z)
  let K : ENNReal := ∫⁻ z, W z ∂μ
  have hfMeas : Measurable f := (measurable_const.mul hS).exp
  have hfENN : Measurable (fun z => ENNReal.ofReal (f z)) :=
    ENNReal.measurable_ofReal.comp hfMeas
  have hfNonneg : ∀ z, 0 ≤ f z := fun z => (Real.exp_pos _).le
  have hSet (t : ℝ) (ht : 0 < t) :
      {z : Ω | t < f z} = {z : Ω | Real.log t / β < S z} := by
    ext z
    change (t < Real.exp (β * S z)) ↔ (Real.log t / β < S z)
    constructor
    · intro hz
      have hl : Real.log t < β * S z := Real.exp_lt_exp.mp (by
        simpa only [Real.exp_log ht] using hz)
      exact (div_lt_iff₀ hβ).2 (by simpa only [mul_comm] using hl)
    · intro hz
      have hl : Real.log t < β * S z := by
        simpa only [mul_comm] using (div_lt_iff₀ hβ).1 hz
      exact (by simpa only [Real.exp_log ht] using Real.exp_lt_exp.mpr hl)
  have hTailF (t : ℝ) (ht : 0 < t) :
      ν {z : Ω | t < f z} =
        μ {z : Ω | t < f z} * K := by
    rw [hSet t ht]
    exact hTail (Real.log t / β)
  have hLayerν :
      (∫⁻ z, ENNReal.ofReal (f z) ∂ν) =
      (∫⁻ t in Ioi (0 : ℝ), ν {z : Ω | t < f z} ∂volume) :=
    lintegral_eq_lintegral_meas_lt ν
      (Filter.Eventually.of_forall hfNonneg) hfMeas.aemeasurable
  have hLayerμ :
      (∫⁻ z, ENNReal.ofReal (f z) ∂μ) =
      (∫⁻ t in Ioi (0 : ℝ), μ {z : Ω | t < f z} ∂volume) :=
    lintegral_eq_lintegral_meas_lt μ
      (Filter.Eventually.of_forall hfNonneg) hfMeas.aemeasurable
  have hOuter :
      (∫⁻ t in Ioi (0 : ℝ), ν {z : Ω | t < f z} ∂volume) =
      (∫⁻ t in Ioi (0 : ℝ), μ {z : Ω | t < f z} * K ∂volume) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    exact hTailF t ht
  have hScale :
      (∫⁻ t in Ioi (0 : ℝ), μ {z : Ω | t < f z} * K ∂volume) =
      (∫⁻ t in Ioi (0 : ℝ), μ {z : Ω | t < f z} ∂volume) * K :=
    lintegral_mul_const' K (fun t => μ {z : Ω | t < f z}) hK
  have hDensity :
      (∫⁻ z, ENNReal.ofReal (f z) ∂ν) =
      (∫⁻ z, W z * ENNReal.ofReal (f z) ∂μ) := by
    simpa only [ν, Pi.mul_apply] using
      (lintegral_withDensity_eq_lintegral_mul μ hW hfENN)
  change (∫⁻ z, W z * ENNReal.ofReal (f z) ∂μ) =
    (∫⁻ z, ENNReal.ofReal (f z) ∂μ) * K
  calc
    _ = (∫⁻ z, ENNReal.ofReal (f z) ∂ν) := hDensity.symm
    _ = (∫⁻ t in Ioi (0 : ℝ), ν {z : Ω | t < f z} ∂volume) := hLayerν
    _ = (∫⁻ t in Ioi (0 : ℝ), μ {z : Ω | t < f z} * K ∂volume) := hOuter
    _ = (∫⁻ t in Ioi (0 : ℝ), μ {z : Ω | t < f z} ∂volume) * K := hScale
    _ = (∫⁻ z, ENNReal.ofReal (f z) ∂μ) * K := by rw [hLayerμ]
