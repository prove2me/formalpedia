-- Prove2me | solution 1 for Cohen2019.Tight.prob_X_mem_B
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T13:57:31.015462+00:00
-- url     : https://prove2.me/submissions/88aaf916-555b-44d1-99f1-49e7dc7ff483

import Mathlib
import Definitions.Def_Cohen2019_Tight_Model
import Definitions.Def_Cohen2019_Tight_HalfSpaces

open MeasureTheory ProbabilityTheory in
theorem edbd_phi_strictMono : StrictMono Cohen2019.Robust.Phi := by
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
theorem edbd_phi_continuous : Continuous Cohen2019.Robust.Phi := by
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
theorem edbd_phi_inv {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Cohen2019.Robust.Phi (Cohen2019.Robust.PhiInvReal q) = q := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot (gaussianReal 0 1)).eventually
    (Iio_mem_nhds hq0)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop (gaussianReal 0 1)).eventually
    (Ioi_mem_nhds hq1)).exists
  have hmem : q ∈ Set.Icc (Cohen2019.Robust.Phi a) (Cohen2019.Robust.Phi b) :=
    ⟨le_of_lt ha, le_of_lt hb⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ a b edbd_phi_continuous hmem
  have hS : {s : ℝ | q ≤ Cohen2019.Robust.Phi s} = Set.Ici t := by
    ext s
    simp only [Set.mem_Ici]
    rw [← ht]
    exact edbd_phi_strictMono.le_iff_le
  unfold Cohen2019.Robust.PhiInvReal
  rw [hS, csInf_Ici, ht]

open MeasureTheory ProbabilityTheory Cohen2019.Tight in
theorem solution {d : ℕ} (x δ : Space d) (σ pB : ℝ) (hσ : 0 < σ) (hδ : δ ≠ 0)
    (hpB0 : 0 < pB) (hpB1 : pB < 1) :
    (gaussNoise x σ (setB x δ σ pB)).toReal = pB := by
  set t := Cohen2019.Robust.PhiInvReal (1 - pB) with ht_def
  have hPhi : Cohen2019.Robust.Phi t = 1 - pB := edbd_phi_inv (by linarith) (by linarith)
  have hnδ : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  set u : Space d := ‖δ‖⁻¹ • δ with hu
  have hun : ‖u‖ = 1 := norm_smul_inv_norm hδ
  set L : StrongDual ℝ (Space d) := innerSL ℝ u with hL
  have hLn : ‖L‖ = 1 := by rw [hL, innerSL_apply_norm, hun]
  have hmeasB : MeasurableSet (setB x δ σ pB) := by
    unfold setB
    exact measurableSet_le measurable_const (by fun_prop)
  have hpre : (fun z : Space d => x + σ • z) ⁻¹' (setB x δ σ pB) = L ⁻¹' Set.Ici t := by
    ext z
    simp only [Set.mem_preimage, setB, Set.mem_Ici, hL, innerSL_apply_apply, hu,
      inner_smul_left]
    change σ * ‖δ‖ * t ≤ inner ℝ δ (x + σ • z - x) ↔ t ≤ (starRingEnd ℝ) ‖δ‖⁻¹ * inner ℝ δ z
    rw [add_sub_cancel_left, inner_smul_right]
    rw [starRingEnd_apply, star_trivial]
    have hpos : 0 < σ * ‖δ‖ := mul_pos hσ hnδ
    have he : σ * inner ℝ δ z = (σ * ‖δ‖) * (‖δ‖⁻¹ * inner ℝ δ z) := by
      field_simp
    rw [he]
    exact mul_le_mul_iff_right₀ hpos
  have hmapL : (stdGaussian (Space d)).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, hLn]
    simp
  unfold gaussNoise
  rw [Measure.map_apply (by fun_prop) hmeasB, hpre,
    ← Measure.map_apply L.continuous.measurable measurableSet_Ici, hmapL]
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have h1 : gaussianReal 0 1 (Set.Ici t) = 1 - gaussianReal 0 1 (Set.Iic t) := by
    rw [← Set.compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, measure_congr Iio_ae_eq_Iic]
  rw [h1, ← ofReal_cdf, ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_one.mpr (cdf_le_one _ _))
    ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.toReal_ofReal (cdf_nonneg _ _)]
  change 1 - Cohen2019.Robust.Phi t = pB
  rw [hPhi]
  ring
