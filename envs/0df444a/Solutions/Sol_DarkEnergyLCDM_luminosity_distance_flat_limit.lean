-- Prove2me | solution 1 for DarkEnergyLCDM.luminosity_distance_flat_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:29:25.139576+00:00
-- url     : https://prove2.me/submissions/0e424f4a-4390-4f5d-bf3a-65c91a35dffd

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

open Filter Topology
open DarkEnergyLCDM

namespace LULum

theorem lim_aux (F : ℝ → ℝ) (d H₀ : ℝ) (hF0 : F 0 = 0) (hd : HasDerivAt F d 0) :
    Tendsto (fun u => F u / (H₀ * u)) (𝓝[≠] 0) (𝓝 (d / H₀)) := by
  have := (hasDerivAt_iff_tendsto_slope.1 hd).div_const H₀
  refine this.congr (fun u => ?_)
  simp only [slope_fun_def_field, hF0, sub_zero]
  rw [div_div, mul_comm]

end LULum

theorem solution (H : ℝ → ℝ) (H₀ : ℝ) (hH₀ : H₀ ≠ 0) (z : ℝ) :
    Tendsto (fun Ωk : ℝ => luminosityDistance H H₀ Ωk z) (𝓝[≠] 0)
      (𝓝 (luminosityDistance H H₀ 0 z)) := by
  set χ := comovingDistance H z with hχ
  have h0 : luminosityDistance H H₀ 0 z = (1 + z) * χ := by
    simp [luminosityDistance, hχ]
  rw [h0, ← nhdsLT_sup_nhdsGT]
  apply Tendsto.sup
  · -- negative side
    have hF : HasDerivAt (fun u => Real.sin (u * H₀ * χ))
        (Real.cos (id 0 * H₀ * χ) * (1 * H₀ * χ)) 0 :=
      (((hasDerivAt_id (0:ℝ)).mul_const H₀).mul_const χ).sin
    have hl := LULum.lim_aux _ _ H₀ (by simp) hF
    have e : Real.cos (id 0 * H₀ * χ) * (1 * H₀ * χ) / H₀ = χ := by
      simp; field_simp
    rw [e] at hl
    have hs : Tendsto (fun Ω : ℝ => Real.sqrt |Ω|) (𝓝[<] 0) (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_iff.2
      constructor
      · have : Tendsto (fun Ω : ℝ => Real.sqrt |Ω|) (𝓝 0) (𝓝 (Real.sqrt |0|)) :=
          (Real.continuous_sqrt.comp continuous_abs).continuousAt.tendsto
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with Ω hΩ
        have : Ω < 0 := hΩ
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact (Real.sqrt_pos.2 (abs_pos.2 this.ne)).ne'
    have := (hl.comp hs).const_mul (1 + z)
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with Ω hΩ
    have : Ω < 0 := hΩ
    simp [luminosityDistance, not_lt.2 this.le, this.ne, hχ]
  · have hF : HasDerivAt (fun u => Real.sinh (u * H₀ * χ))
        (Real.cosh (id 0 * H₀ * χ) * (1 * H₀ * χ)) 0 :=
      (((hasDerivAt_id (0:ℝ)).mul_const H₀).mul_const χ).sinh
    have hl := LULum.lim_aux _ _ H₀ (by simp) hF
    have e : Real.cosh (id 0 * H₀ * χ) * (1 * H₀ * χ) / H₀ = χ := by
      simp; field_simp
    rw [e] at hl
    have hs : Tendsto (fun Ω : ℝ => Real.sqrt Ω) (𝓝[>] 0) (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_iff.2
      constructor
      · have : Tendsto (fun Ω : ℝ => Real.sqrt Ω) (𝓝 0) (𝓝 (Real.sqrt 0)) :=
          Real.continuous_sqrt.continuousAt.tendsto
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with Ω hΩ
        have : 0 < Ω := hΩ
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact (Real.sqrt_pos.2 this).ne'
    have := (hl.comp hs).const_mul (1 + z)
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with Ω hΩ
    have : 0 < Ω := hΩ
    simp [luminosityDistance, this, hχ]
