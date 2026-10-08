-- Prove2me | solution 1 for Cohen2019.Tight.prob_X_mem_A
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:47:46.190042+00:00
-- url     : https://prove2.me/submissions/aab64489-51a5-4c8d-a815-b0b22ea47a30

import Mathlib
import Definitions.Def_Cohen2019_Tight_Model
import Definitions.Def_Cohen2019_Tight_HalfSpaces

set_option autoImplicit false

open MeasureTheory ProbabilityTheory in
theorem pxa_phi_strictMono : StrictMono Cohen2019.Robust.Phi := by
  intro a b hab
  unfold Cohen2019.Robust.Phi
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  have hpos : (gaussianReal 0 1) (Set.Ioc a b) ≠ 0 := by
    intro h
    have h2 := gaussianReal_absolutelyContinuous' (0 : ℝ) hv h
    rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at h2
    linarith
  have hm := (cdf (gaussianReal 0 1)).measure_Ioc a b
  rw [measure_cdf] at hm
  rw [hm] at hpos
  have : ¬ (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a ≤ 0) := by
    intro hle; exact hpos (ENNReal.ofReal_eq_zero.mpr hle)
  linarith

open MeasureTheory ProbabilityTheory in
theorem pxa_phi_continuous : Continuous Cohen2019.Robust.Phi := by
  have hfun : Cohen2019.Robust.Phi = fun t => cdf (gaussianReal 0 1) t := rfl
  rw [hfun, continuous_iff_continuousAt]
  intro a
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [(monotone_cdf (gaussianReal 0 1)).continuousAt_iff_leftLim_eq_rightLim,
    StieltjesFunction.rightLim_eq]
  have hs := (cdf (gaussianReal 0 1)).measure_singleton a
  rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero] at hs
  have hle := (monotone_cdf (gaussianReal 0 1)).leftLim_le (le_refl a)
  linarith

open MeasureTheory ProbabilityTheory Filter in
theorem pxa_phi_inv {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Cohen2019.Robust.Phi (Cohen2019.Robust.PhiInvReal q) = q := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot (gaussianReal 0 1)).eventually
    (Iio_mem_nhds hq0)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop (gaussianReal 0 1)).eventually
    (Ioi_mem_nhds hq1)).exists
  have hmem : q ∈ Set.Icc (Cohen2019.Robust.Phi a) (Cohen2019.Robust.Phi b) :=
    ⟨le_of_lt ha, le_of_lt hb⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ a b pxa_phi_continuous hmem
  have hS : {s : ℝ | q ≤ Cohen2019.Robust.Phi s} = Set.Ici t := by
    ext s
    simp only [Set.mem_Ici]
    rw [← ht]
    exact pxa_phi_strictMono.le_iff_le
  unfold Cohen2019.Robust.PhiInvReal
  rw [hS, csInf_Ici, ht]

open MeasureTheory ProbabilityTheory Cohen2019.Tight in
theorem pxa_law {d : ℕ} (x δ : Space d) (σ : ℝ) (hσ : 0 < σ) (hδ : δ ≠ 0) (S : Set ℝ)
    (hS : MeasurableSet S) :
    gaussNoise x σ ((fun z : Space d => inner ℝ δ (z - x) / (σ * ‖δ‖)) ⁻¹' S)
      = gaussianReal 0 1 S := by
  have hnδ : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  set u : Space d := ‖δ‖⁻¹ • δ with hu
  have hun : ‖u‖ = 1 := norm_smul_inv_norm hδ
  set L : StrongDual ℝ (Space d) := innerSL ℝ u with hL
  have hLn : ‖L‖ = 1 := by rw [hL, innerSL_apply_norm, hun]
  have hmapL : (stdGaussian (Space d)).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, hLn]
    simp
  have hmh : Measurable (fun z : Space d => inner ℝ δ (z - x) / (σ * ‖δ‖)) := by fun_prop
  have hkey : ∀ z : Space d, inner ℝ δ (x + σ • z - x) / (σ * ‖δ‖) = L z := by
    intro z
    simp only [hL, innerSL_apply_apply, hu, inner_smul_left, add_sub_cancel_left,
      inner_smul_right, starRingEnd_apply, star_trivial]
    field_simp
  have hpre : (fun z : Space d => x + σ • z) ⁻¹'
      ((fun z : Space d => inner ℝ δ (z - x) / (σ * ‖δ‖)) ⁻¹' S) = L ⁻¹' S := by
    ext z
    simp only [Set.mem_preimage]
    rw [hkey z]
  unfold gaussNoise
  rw [Measure.map_apply (by fun_prop) (hmh hS), hpre,
    ← Measure.map_apply L.continuous.measurable hS, hmapL]

open MeasureTheory ProbabilityTheory Cohen2019.Tight in
theorem solution {d : ℕ} (x δ : Space d) (σ pA : ℝ) (hσ : 0 < σ) (hδ : δ ≠ 0)
    (hpA0 : 0 < pA) (hpA1 : pA < 1) :
    (gaussNoise x σ (setA x δ σ pA)).toReal = pA := by
  have hnδ : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  have hk : 0 < σ * ‖δ‖ := mul_pos hσ hnδ
  set c := Cohen2019.Robust.PhiInvReal pA with hc
  have hPc : Cohen2019.Robust.Phi c = pA := pxa_phi_inv hpA0 hpA1
  have hset : setA x δ σ pA =
      (fun z : Space d => inner ℝ δ (z - x) / (σ * ‖δ‖)) ⁻¹' Set.Iic c := by
    ext z
    simp only [setA, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic]
    rw [div_le_iff₀ hk, ← hc]
    constructor <;> intro h <;> linarith
  rw [hset, pxa_law x δ σ hσ hδ (Set.Iic c) measurableSet_Iic, ← hPc]
  unfold Cohen2019.Robust.Phi
  rw [cdf_eq_real]
  rfl
