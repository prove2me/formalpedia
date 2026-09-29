-- Prove2me | solution 1 for DysonGraviton.strain_eq
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T03:36:26.713375+00:00
-- url     : https://prove2.me/submissions/be5f08e6-e4a2-4634-9795-978d9fc519b6

import Definitions.Def_DysonGraviton_Defs
import Mathlib

open MeasureTheory Filter Topology
open DysonGraviton

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem W6_DysonGraviton_coherenceLength_eq (α B Hc c ω : ℝ) (hα : 0 < α) (hB : 0 < B)
    (hHc : 0 < Hc) (hc : 0 < c) (hω : 0 < ω) :
    coherenceLength 4 α B Hc c ω = 90 * Real.pi ^ 2 * c * Hc ^ 2 / (α * B ^ 2 * ω) := by
  unfold coherenceLength photonSlowdown
  have := Real.pi_pos
  field_simp
  ring

theorem W6_DysonGraviton_ratio_sq (G B c D : ℝ) (hG : 0 < G) (hc : 0 < c) :
    (D / mixingLength G B c) ^ 2 = G * B ^ 2 * D ^ 2 / (4 * c ^ 4) := by
  unfold mixingLength
  rcases eq_or_ne B 0 with rfl | hB
  · simp
  have hsG : 0 < Real.sqrt G := Real.sqrt_pos.2 hG
  rw [div_div_eq_mul_div, div_pow, mul_pow, mul_pow, Real.sq_sqrt hG.le]
  field_simp
  ring

theorem W6_DysonGraviton_prob_le (G B c D : ℝ) (hG : 0 < G) (hc : 0 < c) :
    conversionProb G B c D ≤ G * B ^ 2 * D ^ 2 / (4 * c ^ 4) := by
  unfold conversionProb
  rw [← W6_DysonGraviton_ratio_sq G B c D hG hc]
  exact Real.sin_sq_le_sq

theorem W6_DysonGraviton_conversionProb_coherent_bound (G α B Hc c ω D : ℝ) (hG : 0 < G) (hα : 0 < α)
    (hB : 0 < B) (hHc : 0 < Hc) (hc : 0 < c) (hω : 0 < ω) (hD : 0 < D)
    (hDL : D ≤ coherenceLength 4 α B Hc c ω) :
    conversionProb G B c D ≤
      2025 * Real.pi ^ 4 * G * Hc ^ 4 / (α ^ 2 * c ^ 2 * B ^ 2 * ω ^ 2) := by
  refine (W6_DysonGraviton_prob_le G B c D hG hc).trans ?_
  rw [W6_DysonGraviton_coherenceLength_eq α B Hc c ω hα hB hHc hc hω] at hDL
  have hD2 : D ^ 2 ≤ (90 * Real.pi ^ 2 * c * Hc ^ 2 / (α * B ^ 2 * ω)) ^ 2 :=
    pow_le_pow_left₀ hD.le hDL 2
  have hk : 0 ≤ G * B ^ 2 / (4 * c ^ 4) := by positivity
  calc G * B ^ 2 * D ^ 2 / (4 * c ^ 4) = G * B ^ 2 / (4 * c ^ 4) * D ^ 2 := by ring
    _ ≤ G * B ^ 2 / (4 * c ^ 4) * (90 * Real.pi ^ 2 * c * Hc ^ 2 / (α * B ^ 2 * ω)) ^ 2 :=
        mul_le_mul_of_nonneg_left hD2 hk
    _ = 2025 * Real.pi ^ 4 * G * Hc ^ 4 / (α ^ 2 * c ^ 2 * B ^ 2 * ω ^ 2) := by
        field_simp
        ring

theorem W6_DysonGraviton_conversionProb_small (G B c : ℝ) (hG : 0 < G) (hB : 0 < B) (hc : 0 < c) :
    (∀ D : ℝ, conversionProb G B c D ≤ G * B ^ 2 * D ^ 2 / (4 * c ^ 4)) ∧
    Tendsto (fun D : ℝ => conversionProb G B c D / (G * B ^ 2 * D ^ 2 / (4 * c ^ 4)))
      (𝓝[>] 0) (𝓝 1) := by
  refine ⟨fun D => W6_DysonGraviton_prob_le G B c D hG hc, ?_⟩
  have hL : 0 < mixingLength G B c := by
    unfold mixingLength; have := Real.sqrt_pos.2 hG; positivity
  have hcont : Tendsto (fun D : ℝ => Real.sinc (D / mixingLength G B c) ^ 2) (𝓝 0) (𝓝 1) := by
    have h1 : Continuous (fun D : ℝ => Real.sinc (D / mixingLength G B c) ^ 2) :=
      (Real.continuous_sinc.comp (continuous_id.div_const _)).pow 2
    have := h1.tendsto 0
    simpa [Real.sinc_zero] using this
  refine (hcont.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with D hD
  have hD' : D ≠ 0 := ne_of_gt hD
  have hx : D / mixingLength G B c ≠ 0 := div_ne_zero hD' hL.ne'
  rw [Real.sinc_of_ne_zero hx, ← W6_DysonGraviton_ratio_sq G B c D hG hc, conversionProb, div_pow]

theorem W6_DysonGraviton_clamped_mirrors_bound (M δ D s c G hbar : ℝ) (hM : 0 < M) (hD : 0 < D)
    (hs : 0 < s) (hsc : s < c) (hG : 0 < G) (hh : 0 < hbar)
    (hzp : hbar * D / (M * s) ≤ δ ^ 2) (hδ : δ = planckLength G hbar c) :
    c / s * D ≤ G * M / c ^ 2 ∧ D < c / s * D := by
  have hc : 0 < c := hs.trans hsc
  subst hδ
  unfold planckLength at hzp
  rw [Real.sq_sqrt (by positivity)] at hzp
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity)] at hzp
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hs (by positivity)]
    have : hbar * (D * c ^ 3) ≤ hbar * (G * M * s) := by nlinarith
    have h2 : D * c ^ 3 ≤ G * M * s := le_of_mul_le_mul_left this hh
    nlinarith
  · rw [div_mul_eq_mul_div, lt_div_iff₀ hs]
    nlinarith

theorem W6_DysonGraviton_free_mirrors_bound (M δ T D c G hbar : ℝ) (hM : 0 < M) (hT : 0 < T)
    (hD : 0 < D) (hc : 0 < c) (hG : 0 < G) (hh : 0 < hbar)
    (hHeis : hbar * T ≤ M * δ ^ 2) (hTD : D / c ≤ T)
    (hδ : δ = planckLength G hbar c) :
    D ≤ G * M / c ^ 2 := by
  subst hδ
  unfold planckLength at hHeis
  rw [Real.sq_sqrt (by positivity)] at hHeis
  rw [div_le_iff₀ hc] at hTD
  have h1 : hbar * T ≤ hbar * (M * G / c ^ 3) := by
    calc hbar * T ≤ M * (G * hbar / c ^ 3) := hHeis
      _ = hbar * (M * G / c ^ 3) := by ring
  have hT' : T ≤ M * G / c ^ 3 := le_of_mul_le_mul_left h1 hh
  rw [le_div_iff₀ (by positivity)]
  have : D ≤ M * G / c ^ 3 * c := hTD.trans (mul_le_mul_of_nonneg_right hT' hc.le)
  have e : M * G / c ^ 3 * c = G * M / c ^ 2 := by field_simp
  rw [e] at this
  calc D * c ^ 2 ≤ G * M / c ^ 2 * c ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
    _ = G * M := by field_simp

theorem W6_DysonGraviton_f_sq (c G hbar ω f : ℝ) (hc : 0 < c) (hG : 0 < G)
    (hh : 0 < hbar) (hω : 0 < ω) (hf : 0 < f)
    (h : gwEnergyDensity c G ω f = singleGravitonEnergyDensity hbar ω c) :
    f = Real.sqrt (32 * Real.pi) * planckLength G hbar c * ω / c := by
  have hpi := Real.pi_pos
  unfold gwEnergyDensity singleGravitonEnergyDensity at h
  have hsq : f ^ 2 = (Real.sqrt (32 * Real.pi) * planckLength G hbar c * ω / c) ^ 2 := by
    unfold planckLength
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    field_simp at h ⊢
    nlinarith [h]
  have hrhs : 0 ≤ Real.sqrt (32 * Real.pi) * planckLength G hbar c * ω / c := by
    unfold planckLength; positivity
  exact (pow_left_inj₀ hf.le hrhs (by norm_num)).1 hsq

theorem solution (c G hbar ω f : ℝ) (hc : 0 < c) (hG : 0 < G) (hh : 0 < hbar)
    (hω : 0 < ω) (hf : 0 < f)
    (h : gwEnergyDensity c G ω f = singleGravitonEnergyDensity hbar ω c) :
    f = Real.sqrt (32 * Real.pi) * planckLength G hbar c * ω / c :=
  W6_DysonGraviton_f_sq c G hbar ω f hc hG hh hω hf h

theorem W6_DysonGraviton_distance_variation_eq (c G hbar ω f : ℝ) (hc : 0 < c) (hG : 0 < G)
    (hh : 0 < hbar) (hω : 0 < ω) (hf : 0 < f)
    (h : gwEnergyDensity c G ω f = singleGravitonEnergyDensity hbar ω c) :
    f * (c / ω) = Real.sqrt (32 * Real.pi) * planckLength G hbar c := by
  rw [W6_DysonGraviton_f_sq c G hbar ω f hc hG hh hω hf h]
  field_simp
