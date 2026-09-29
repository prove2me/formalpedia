-- Prove2me | solution 1 for Complex.isOpen_image_and_exists_differentiableOn_leftInverse_of_injOn_ball
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c05992b8-9023-5140-8a04-decdafdcc10e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_isOpen_image_and_exists_differentiableOn_leftInverse_of_injOn_ball

set_option autoImplicit false

open Topology Filter

theorem deriv_ne_zero_of_injOn_of_isOpen {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U) {z₁ : ℂ} (hz₁ : z₁ ∈ U) :
    deriv f z₁ ≠ 0 := by
  intro hd
  have hfa : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU
  have hfz : AnalyticAt ℂ f z₁ := hfa z₁ hz₁
  set h : ℂ → ℂ := fun z => f z - f z₁ with hh
  have hha : AnalyticAt ℂ h z₁ := hfz.sub analyticAt_const

  have hU1 : U ∈ 𝓝 z₁ := hU.mem_nhds hz₁
  have hne : ¬ ∀ᶠ z in 𝓝 z₁, h z = 0 := by
    intro hev
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hev.and (Filter.eventually_mem_set.mpr hU1))

    have hmem : z₁ + (r / 2 : ℝ) ∈ Metric.ball z₁ r := by
      rw [Metric.mem_ball, dist_self_add_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    have h1 := hball hmem
    have h0 := hball (Metric.mem_ball_self hr)
    simp only [Set.mem_setOf_eq] at h1 h0
    have hEq : f (z₁ + (r / 2 : ℝ)) = f z₁ := by
      have := h1.1; simp only [hh, sub_eq_zero] at this; exact this
    have := hinj h1.2 h0.2 hEq
    have : (r / 2 : ℝ) = 0 := by
      have h' : ((r / 2 : ℝ) : ℂ) = 0 := by linear_combination this
      exact_mod_cast h'
    linarith
  obtain ⟨n, u, hua, hu0, hev0⟩ := (hha.exists_eventuallyEq_pow_smul_nonzero_iff).mpr hne
  have hev : h =ᶠ[𝓝 z₁] fun z => (z - z₁) ^ n • u z := hev0

  have hn0 : n ≠ 0 := by
    intro hn
    have h0 : h z₁ = (z₁ - z₁) ^ n • u z₁ := hev.eq_of_nhds
    simp only [hh, sub_self, hn, pow_zero, one_smul] at h0
    exact hu0 h0.symm

  have hn1 : n ≠ 1 := by
    intro hn
    have hderiv : deriv h z₁ = u z₁ := by
      rw [hev.deriv_eq]
      have hu' : HasDerivAt u (deriv u z₁) z₁ := hua.differentiableAt.hasDerivAt
      have hlin : HasDerivAt (fun z : ℂ => z - z₁) 1 z₁ := (hasDerivAt_id z₁).sub_const z₁
      have hprod : HasDerivAt (fun z : ℂ => (z - z₁) * u z) (1 * u z₁ + (z₁ - z₁) * deriv u z₁) z₁ :=
        hlin.mul hu'
      simp only [hn, pow_one, smul_eq_mul]
      rw [hprod.deriv]
      simp
    have hdh : deriv h z₁ = deriv f z₁ := by
      simp only [hh, deriv_sub_const]
    rw [hdh, hd] at hderiv
    exact hu0 hderiv.symm
  have hn2 : 2 ≤ n := by omega

  set v : ℂ → ℂ := fun z => (u z₁) ^ ((n : ℂ)⁻¹) * Complex.exp ((n : ℂ)⁻¹ * Complex.log (u z / u z₁)) with hv
  have hva : AnalyticAt ℂ v z₁ := by
    have h1 : AnalyticAt ℂ (fun z => u z / u z₁) z₁ := hua.div analyticAt_const hu0
    have h2 : AnalyticAt ℂ (fun z => Complex.log (u z / u z₁)) z₁ := by
      refine h1.clog ?_
      show u z₁ / u z₁ ∈ Complex.slitPlane
      rw [div_self hu0]
      exact Complex.one_mem_slitPlane
    exact analyticAt_const.mul ((analyticAt_const.mul h2).cexp)
  have hvpow : ∀ᶠ z in 𝓝 z₁, v z ^ n = u z := by

    have hune : ∀ᶠ z in 𝓝 z₁, u z ≠ 0 := hua.continuousAt.eventually_ne hu0
    filter_upwards [hune] with z hz
    have hq : u z / u z₁ ≠ 0 := div_ne_zero hz hu0
    simp only [hv, mul_pow]
    rw [← Complex.exp_nat_mul, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn0), one_mul,
      Complex.exp_log hq, Complex.cpow_nat_inv_pow _ hn0]
    field_simp
  set ψ : ℂ → ℂ := fun z => (z - z₁) * v z with hψ
  have hψa : AnalyticAt ℂ ψ z₁ := ((analyticAt_id).sub analyticAt_const).mul hva
  have hψ0 : ψ z₁ = 0 := by simp [hψ]
  have hhψ : ∀ᶠ z in 𝓝 z₁, h z = ψ z ^ n := by
    filter_upwards [hev, hvpow] with z h1 h2
    rw [h1, smul_eq_mul, hψ, mul_pow, h2]

  have hψnc : ¬ ∀ᶠ z in 𝓝 z₁, ψ z = ψ z₁ := by
    intro hcst
    apply hne
    filter_upwards [hcst, hhψ] with z h1 h2
    rw [h2, h1, hψ0, zero_pow hn0]
  have hmap : 𝓝 (ψ z₁) ≤ Filter.map ψ (𝓝 z₁) :=
    (hψa.eventually_constant_or_nhds_le_map_nhds).resolve_left hψnc

  obtain ⟨N, hN, hNsub⟩ : ∃ N ∈ 𝓝 z₁, ∀ z ∈ N, z ∈ U ∧ h z = ψ z ^ n := by
    exact ⟨_, (Filter.eventually_mem_set.mpr hU1).and hhψ, fun z hz => hz⟩
  have himg : ψ '' N ∈ 𝓝 (0 : ℂ) := by
    rw [← hψ0]
    exact hmap (Filter.image_mem_map hN)
  obtain ⟨r, hr, hballr⟩ := Metric.mem_nhds_iff.mp himg

  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hζ
  have hprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  have hζ1 : ζ ≠ 1 := hprim.ne_one hn2
  have hζn : ζ ^ n = 1 := hprim.pow_eq_one
  have hζnorm : ‖ζ‖ = 1 := hprim.norm'_eq_one hn0
  set t : ℂ := ((r / 2 : ℝ) : ℂ) with ht
  have ht0 : t ≠ 0 := by
    simp only [ht, ne_eq, Complex.ofReal_eq_zero]; linarith
  have htmem : t ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, ht, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have htζmem : t * ζ ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hζnorm, mul_one, ht, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  obtain ⟨a, haN, hψa'⟩ := hballr htmem
  obtain ⟨b, hbN, hψb'⟩ := hballr htζmem
  have hab : a ≠ b := by
    intro habeq
    have htt : t = t * ζ := by
      calc t = ψ a := hψa'.symm
        _ = ψ b := by rw [habeq]
        _ = t * ζ := hψb'
    have hz1 : ζ = 1 := by
      have h' := htt.symm
      rwa [mul_eq_left₀ ht0] at h'
    exact hζ1 hz1
  have hha' : h a = h b := by
    rw [(hNsub a haN).2, (hNsub b hbN).2, hψa', hψb', mul_pow, hζn, mul_one]
  have hfab : f a = f b := by
    simp only [hh] at hha'
    linear_combination hha'
  exact hab (hinj (hNsub a haN).1 (hNsub b hbN).1 hfab)

theorem solution
    (f : ℂ → ℂ) (z₀ : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ ε)) (hinj : Set.InjOn f (Metric.ball z₀ ε)) :
    IsOpen (f '' Metric.ball z₀ ε) ∧
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (f '' Metric.ball z₀ ε) ∧
      (∀ z ∈ Metric.ball z₀ ε, g (f z) = z) ∧
      (∀ w ∈ f '' Metric.ball z₀ ε, g w ∈ Metric.ball z₀ ε ∧ f (g w) = w) := by
  have hDo : IsOpen (Metric.ball z₀ ε) := Metric.isOpen_ball
  have hfa : AnalyticOnNhd ℂ f (Metric.ball z₀ ε) := hf.analyticOnNhd hDo

  have hopen : ∀ s ⊆ Metric.ball z₀ ε, IsOpen s → IsOpen (f '' s) := by
    rcases hfa.is_constant_or_isOpen (convex_ball z₀ ε).isPreconnected with ⟨w, hw⟩ | h
    · exfalso
      have h0 : z₀ ∈ Metric.ball z₀ ε := Metric.mem_ball_self hε
      have h1 : z₀ + (ε / 2 : ℝ) ∈ Metric.ball z₀ ε := by
        rw [Metric.mem_ball, dist_self_add_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      have := hinj h1 h0 ((hw _ h1).trans (hw _ h0).symm)
      have : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination this
      have : (ε / 2 : ℝ) = 0 := by exact_mod_cast this
      linarith
    · exact h
  refine ⟨hopen _ subset_rfl hDo, ?_⟩
  refine ⟨Function.invFunOn f (Metric.ball z₀ ε), ?_, fun z hz => hinj.leftInvOn_invFunOn hz,
    fun w hw => Function.invFunOn_pos hw⟩

  set g := Function.invFunOn f (Metric.ball z₀ ε) with hg
  have hg1 : ∀ z ∈ Metric.ball z₀ ε, g (f z) = z := fun z hz => hinj.leftInvOn_invFunOn hz
  have hg2 : ∀ w ∈ f '' Metric.ball z₀ ε, g w ∈ Metric.ball z₀ ε ∧ f (g w) = w :=
    fun w hw => Function.invFunOn_pos hw
  have hWo : IsOpen (f '' Metric.ball z₀ ε) := hopen _ subset_rfl hDo

  have hgc : ContinuousOn g (f '' Metric.ball z₀ ε) := by
    rw [continuousOn_open_iff hWo]
    intro t ht
    have : f '' Metric.ball z₀ ε ∩ g ⁻¹' t = f '' (Metric.ball z₀ ε ∩ t) := by
      ext w
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hgt⟩
        refine ⟨z, ⟨hz, ?_⟩, rfl⟩
        have : g (f z) = z := hg1 z hz
        simpa [this] using hgt
      · rintro ⟨z, ⟨hz, hzt⟩, rfl⟩
        refine ⟨⟨z, hz, rfl⟩, ?_⟩
        show g (f z) ∈ t
        rw [hg1 z hz]; exact hzt
    rw [this]
    exact hopen _ Set.inter_subset_left (hDo.inter ht)
  intro w hw
  have hgw := hg2 w hw
  have hfd : HasDerivAt f (deriv f (g w)) (g w) :=
    ((hf (g w) hgw.1).differentiableAt (hDo.mem_nhds hgw.1)).hasDerivAt
  have hne : deriv f (g w) ≠ 0 := deriv_ne_zero_of_injOn_of_isOpen hDo hf hinj hgw.1
  have hga : ContinuousAt g w := hgc.continuousAt (hWo.mem_nhds hw)
  have hfg : ∀ᶠ y in 𝓝 w, f (g y) = y := by
    filter_upwards [hWo.mem_nhds hw] with y hy
    exact (hg2 y hy).2
  exact (hfd.of_local_left_inverse hga hne hfg).differentiableAt.differentiableWithinAt

end S_Complex_isOpen_image_and_exists_differentiableOn_leftInverse_of_injOn_ball
end P2MW
export P2MW.S_Complex_isOpen_image_and_exists_differentiableOn_leftInverse_of_injOn_ball (solution)
