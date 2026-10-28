-- Prove2me | solution 1 for ErlangA.Diffusion.infinitesimal_moments_limit
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:05:31.319094+00:00
-- url     : https://prove2.me/submissions/4bbfc2d8-b4c9-49ec-94c5-b30009855a81

import Mathlib
import Definitions.Def_ErlangA_Diffusion_SDE
import Definitions.Def_ErlangA_Diffusion_InfinitesimalMoments

open Filter Topology

open ErlangA.Diffusion in
theorem solution (μ β θ : ℝ) (hμ : 0 < μ) (hθ : 0 < θ)
    (lam thetaN : ℕ → ℝ)
    (hβ : Tendsto (fun N : ℕ => Real.sqrt N * (1 - lam N / (N * μ))) atTop (𝓝 β))
    (hθN : Tendsto thetaN atTop (𝓝 θ)) (x : ℝ) :
    Tendsto (fun N : ℕ => infMean lam thetaN μ N x) atTop (𝓝 (drift μ β θ x)) ∧
    Tendsto (fun N : ℕ => infVar lam thetaN μ N x) atTop (𝓝 (2 * μ)) := by
  set a : ℕ → ℝ := fun N => Real.sqrt N * (1 - lam N / (N * μ)) with ha
  set s : ℕ → ℝ := fun N => Real.sqrt N with hsdef
  have hs : Tendsto s atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N => (s N)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hs
  have hfr : ∀ g : ℕ → ℝ, Tendsto (fun N => Int.fract (g N) / s N) atTop (𝓝 0) := by
    intro g
    refine squeeze_zero' ?_ ?_ hinv
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact div_nonneg (Int.fract_nonneg _) (Real.sqrt_nonneg _)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hpos : 0 < s N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.mpr hpos.le) (Int.fract_lt_one _).le
  have hfloor_div : Tendsto (fun N => (⌊s N * x⌋ : ℝ) / s N) atTop (𝓝 x) := by
    have := (tendsto_const_nhds (x := x)).sub (hfr (fun N => s N * x))
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hpos : 0 < s N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
    rw [← Int.self_sub_fract]
    field_simp
  have hpos : ∀ N : ℕ, 1 ≤ N → 0 < s N := fun N hN => Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hsq : ∀ N : ℕ, s N * s N = N := fun N => Real.mul_self_sqrt (Nat.cast_nonneg N)
  -- λ_N in terms of a_N
  have hlam : ∀ N : ℕ, 1 ≤ N → lam N = N * μ - μ * s N * a N := by
    intro N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have h2 := hsq N
    have hNμ : (N : ℝ) * μ ≠ 0 := by positivity
    have : μ * s N * a N = N * μ - lam N := by
      simp only [ha]
      rw [show μ * s N * (Real.sqrt N * (1 - lam N / (N * μ))) =
        μ * (s N * s N) * (1 - lam N / (N * μ)) by simp only [hsdef]; ring, h2]
      field_simp <;> ring
    linarith
  have hlamS : Tendsto (fun N => lam N / s N - μ * s N) atTop (𝓝 (-(μ * β))) := by
    have := (hβ.const_mul μ).neg
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [hlam N hN]
    simp only [ha, hsdef]
    set r := Real.sqrt (N : ℝ) with hr
    have hp : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast hN)
    have h2 : (N : ℝ) = r ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg N)).symm
    rw [h2]
    field_simp <;> ring
  have hlamN : Tendsto (fun N => lam N / N) atTop (𝓝 μ) := by
    have h1 : Tendsto (fun N : ℕ => μ - μ * (a N * (s N)⁻¹)) atTop (𝓝 (μ - μ * (β * 0))) :=
      tendsto_const_nhds.sub ((hβ.mul hinv).const_mul μ)
    simp only [mul_zero, sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [hlam N hN]
    simp only [hsdef]
    set r := Real.sqrt (N : ℝ) with hr
    have hp : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast hN)
    have h2 : (N : ℝ) = r ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg N)).symm
    rw [h2]
    field_simp <;> ring
  by_cases hx : x ≤ 0
  · have hdr : drift μ β θ x = -(μ * (β + x)) := by unfold drift; rw [if_pos hx]
    rw [hdr]
    constructor
    · have h1 : Tendsto (fun N : ℕ => -(μ * x) + μ * (Int.fract ((N : ℝ) + s N * x) / s N) +
          (lam N / s N - μ * s N)) atTop (𝓝 (-(μ * x) + μ * 0 + -(μ * β))) :=
        (tendsto_const_nhds.add ((hfr _).const_mul μ)).add hlamS
      rw [show -(μ * x) + μ * 0 + -(μ * β) = -(μ * (β + x)) by ring] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      unfold infMean
      rw [if_pos hx]
      rw [← Int.self_sub_fract ((N : ℝ) + Real.sqrt N * x)]
      simp only [hsdef]
      set r := Real.sqrt (N : ℝ) with hr
      have hp : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast hN)
      have h2 : (N : ℝ) = r ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg N)).symm
      rw [h2]
      field_simp <;> ring
    · have h1 : Tendsto (fun N : ℕ => μ + μ * (x * (s N)⁻¹) - μ * (Int.fract ((N : ℝ) + s N * x) / s N
          * (s N)⁻¹) + lam N / N) atTop (𝓝 (μ + μ * (x * 0) - μ * (0 * 0) + μ)) :=
        ((tendsto_const_nhds.add ((tendsto_const_nhds.mul hinv).const_mul μ)).sub
          (((hfr _).mul hinv).const_mul μ)).add hlamN
      rw [show μ + μ * (x * 0) - μ * (0 * 0) + μ = 2 * μ by ring] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      unfold infVar
      rw [if_pos hx]
      rw [← Int.self_sub_fract ((N : ℝ) + Real.sqrt N * x)]
      simp only [hsdef]
      set r := Real.sqrt (N : ℝ) with hr
      have hp : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast hN)
      have h2 : (N : ℝ) = r ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg N)).symm
      rw [h2]
      field_simp <;> ring
  · push_neg at hx
    have hdr : drift μ β θ x = -(μ * β + θ * x) := by unfold drift; rw [if_neg (not_le.mpr hx)]
    rw [hdr]
    constructor
    · have h1 : Tendsto (fun N : ℕ => -((⌊s N * x⌋ : ℝ) / s N * thetaN N) + (lam N / s N - μ * s N))
          atTop (𝓝 (-(x * θ) + -(μ * β))) :=
        (hfloor_div.mul hθN).neg.add hlamS
      rw [show -(x * θ) + -(μ * β) = -(μ * β + θ * x) by ring] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      unfold infMean
      rw [if_neg (not_le.mpr hx)]
      simp only [hsdef]
      set r := Real.sqrt (N : ℝ) with hr
      have hp : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast hN)
      have h2 : (N : ℝ) = r ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg N)).symm
      rw [h2]
      field_simp <;> ring
    · have h1 : Tendsto (fun N : ℕ => μ + (⌊s N * x⌋ : ℝ) / s N * (s N)⁻¹ * thetaN N + lam N / N)
          atTop (𝓝 (μ + x * 0 * θ + μ)) :=
        ((tendsto_const_nhds.add ((hfloor_div.mul hinv).mul hθN))).add hlamN
      rw [show μ + x * 0 * θ + μ = 2 * μ by ring] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      unfold infVar
      rw [if_neg (not_le.mpr hx)]
      simp only [hsdef]
      set r := Real.sqrt (N : ℝ) with hr
      have hp : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast hN)
      have h2 : (N : ℝ) = r ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg N)).symm
      rw [h2]
      field_simp <;> ring
