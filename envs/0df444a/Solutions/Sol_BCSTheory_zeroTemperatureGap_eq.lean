-- Prove2me | solution 1 for BCSTheory.zeroTemperatureGap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-11T06:38:58.528994+00:00
-- url     : https://prove2.me/submissions/ed39d878-be38-4dff-be91-e77cd6d06468

import Mathlib
import Definitions.Def_BCSTheory_GapEquation
open Filter Topology

open Filter Topology

namespace BCSAux
open BCSTheory

theorem gapIntegralZeroTemp_eq_arsinh (hbarOmegaD Δ : ℝ) (hω : 0 < hbarOmegaD)
    (hΔ : 0 < Δ) :
    gapIntegralZeroTemp hbarOmegaD Δ = Real.arsinh (hbarOmegaD / Δ) := by
  unfold gapIntegralZeroTemp quasiparticleEnergy
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) hbarOmegaD,
      HasDerivAt (fun η => Real.arsinh (η / Δ)) (1 / Real.sqrt (x ^ 2 + Δ ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun η => Real.arsinh (η / Δ))
        ((Real.sqrt (1 + (x / Δ) ^ 2))⁻¹ • (1 / Δ)) x :=
      ((hasDerivAt_id x).div_const Δ).arsinh
    convert h1 using 1
    have hpos : 0 < x ^ 2 + Δ ^ 2 := by positivity
    have : Real.sqrt (1 + (x / Δ) ^ 2) = Real.sqrt (x ^ 2 + Δ ^ 2) / Δ := by
      have e : 1 + (x / Δ) ^ 2 = (x ^ 2 + Δ ^ 2) / Δ ^ 2 := by
        field_simp; ring
      rw [e, Real.sqrt_div' _ (sq_nonneg Δ), Real.sqrt_sq hΔ.le]
    rw [this, smul_eq_mul]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro x _
      positivity

theorem zeroTemperatureGap_eq (hbarOmegaD coupling : ℝ) (hω : 0 < hbarOmegaD)
    (hc : 0 < coupling) :
    (∀ Δ : ℝ, 0 < Δ →
      (gapIntegralZeroTemp hbarOmegaD Δ = 1 / coupling ↔
        Δ = hbarOmegaD / Real.sinh (1 / coupling))) ∧
    zeroTemperatureGap hbarOmegaD coupling = hbarOmegaD / Real.sinh (1 / coupling) := by
  have hs : 0 < Real.sinh (1 / coupling) := Real.sinh_pos_iff.mpr (by positivity)
  have key : ∀ Δ : ℝ, 0 < Δ →
      (gapIntegralZeroTemp hbarOmegaD Δ = 1 / coupling ↔
        Δ = hbarOmegaD / Real.sinh (1 / coupling)) := by
    intro Δ hΔ
    rw [gapIntegralZeroTemp_eq_arsinh _ _ hω hΔ]
    constructor
    · intro h
      have := congrArg Real.sinh h
      rw [Real.sinh_arsinh] at this
      rw [← this]
      field_simp
    · intro h
      rw [h, div_div_cancel₀ hω.ne', Real.arsinh_sinh]
  refine ⟨key, ?_⟩
  unfold zeroTemperatureGap
  have : {Δ : ℝ | 0 < Δ ∧ gapIntegralZeroTemp hbarOmegaD Δ = 1 / coupling} =
      {hbarOmegaD / Real.sinh (1 / coupling)} := by
    ext Δ
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact (key Δ h1).mp h2
    · intro h
      have hp : 0 < Δ := by rw [h]; positivity
      exact ⟨hp, (key Δ hp).mpr h⟩
  rw [this, csSup_singleton]

theorem zeroTemperatureGap_weak_coupling (hbarOmegaD : ℝ) (hω : 0 < hbarOmegaD) :
    Tendsto (fun coupling : ℝ =>
        zeroTemperatureGap hbarOmegaD coupling / (2 * hbarOmegaD * Real.exp (-1 / coupling)))
      (𝓝[>] 0) (𝓝 1) := by
  have hlim : Tendsto (fun coupling : ℝ => Real.exp (-1 / coupling)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun coupling : ℝ => -1 / coupling) (𝓝[>] 0) atBot := by
      have h := tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
      convert tendsto_neg_atTop_atBot.comp h using 1
      ext x
      simp [div_eq_mul_inv]
    exact Real.tendsto_exp_atBot.comp this
  have h2 : Tendsto (fun coupling : ℝ => (1 - Real.exp (-1 / coupling) ^ 2)⁻¹) (𝓝[>] 0)
      (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1:ℝ))).sub (hlim.pow 2)).inv₀ (by norm_num)
    simpa using this
  apply h2.congr'
  filter_upwards [self_mem_nhdsWithin] with c (hc : 0 < c)
  rw [(zeroTemperatureGap_eq hbarOmegaD c hω hc).2, Real.sinh_eq]
  have e2 : Real.exp (1 / c) = (Real.exp (-1 / c))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  have e3 : Real.exp (-(1 / c)) = Real.exp (-1 / c) := by ring_nf
  rw [e2, e3]
  have hpos := Real.exp_pos (-1 / c)
  have hlt : Real.exp (-1 / c) < 1 := Real.exp_lt_one_iff.mpr (by
      have : 0 < 1 / c := by positivity
      rw [neg_div]; linarith)
  generalize Real.exp (-1 / c) = u at hpos hlt ⊢
  have h1 : 1 - u ^ 2 ≠ 0 := by nlinarith
  have h4 : u⁻¹ - u ≠ 0 := by
    intro h
    have := mul_inv_cancel₀ hpos.ne'
    nlinarith
  field_simp

end BCSAux
open BCSTheory BCSAux

theorem solution (hbarOmegaD coupling : ℝ) (hω : 0 < hbarOmegaD)
    (hc : 0 < coupling) :
    (∀ Δ : ℝ, 0 < Δ →
      (gapIntegralZeroTemp hbarOmegaD Δ = 1 / coupling ↔
        Δ = hbarOmegaD / Real.sinh (1 / coupling))) ∧
    zeroTemperatureGap hbarOmegaD coupling = hbarOmegaD / Real.sinh (1 / coupling) :=
  BCSAux.zeroTemperatureGap_eq hbarOmegaD coupling hω hc
