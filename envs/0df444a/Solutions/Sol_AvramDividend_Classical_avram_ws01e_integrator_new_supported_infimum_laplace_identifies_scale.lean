-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_integrator_new_supported_infimum_laplace_identifies_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:58:38.671044+00:00
-- url     : https://prove2.me/submissions/45cf2eb0-ae22-4958-a940-e1e834a759be

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
import Theorems.Thm_AvramDividend_Classical_levy_esscher_root_scale_tilted_laplace
import Theorems.Thm_AvramDividend_Classical_positive_cumulative_laplace_real_integral_bridge
import Theorems.Thm_AvramDividend_Classical_rightContinuous_cumulative_toReal_of_finite
import Theorems.Thm_AvramDividend_Classical_continuous_rightContinuous_Ioi_eq_of_laplace_eq
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_strictly_above_shift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hνSupp : ν (Iio 0) = 0)
    (m : ℝ) (hm : 0 < m)
    (hνLap : ∀ β : ℝ, 0 < β →
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ν) =
        ENNReal.ofReal (m * β / (X.ψ (φ + β) - q)))
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x →
      ν (Iic x) = ENNReal.ofReal
        (m * Real.exp (-(φ * x)) * W x) := by
  classical
  let f : ℝ → ℝ := fun x => m * (Real.exp (-φ * x) * W x)
  let g : ℝ → ℝ := fun x => (ν (Iic x)).toReal
  have hνfin (x : ℝ) : ν (Iic x) ≠ ⊤ := measure_ne_top ν (Iic x)
  have hfcont : ContinuousOn f (Ioi 0) := by
    intro x hx
    have hWcont : ContinuousAt W x :=
      scaleFunction_continuousAt_away_zero X q W hW x
        (ne_of_gt hx)
    fun_prop
  have hfnonneg : ∀ x : ℝ, 0 < x → 0 ≤ f x := by
    intro x hx
    have hWx : 0 ≤ W x := hW.2.1 x (le_of_lt hx)
    dsimp [f]
    positivity
  have hgmono : Monotone g := by
    intro x y hxy
    dsimp [g]
    exact ENNReal.toReal_mono (hνfin y)
      (measure_mono (Iic_subset_Iic.mpr hxy))
  have hgmeas : AEMeasurable g (volume.restrict (Ioi (0 : ℝ))) := hgmono.measurable.aemeasurable
  have hgright : ∀ x : ℝ, 0 < x →
      ContinuousWithinAt g (Ici x) x := by
    intro x hx
    simpa only [g] using rightContinuous_cumulative_toReal_of_finite ν hνfin x
  have hgnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x := fun _ _ => ENNReal.toReal_nonneg
  have hlap (β : ℝ) (hβ : 0 < β) :
      IntegrableOn
        (fun x : ℝ => Real.exp (-β * x) * f x) (Ioi 0) ∧
      IntegrableOn
        (fun x : ℝ => Real.exp (-β * x) * g x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-β * x) * f x) =
        (∫ x in Ioi (0 : ℝ), Real.exp (-β * x) * g x) := by
    have hψ : q < X.ψ (φ + β) :=
      levy_psi_root_strictly_above_shift X q φ β hq hφ hβ hroot
    obtain ⟨hscaleInt, hscaleReal⟩ :=
      levy_esscher_root_scale_tilted_laplace
        X q φ β hq hφ hβ hroot W hW
    have hscaleInt' : IntegrableOn
        (fun x : ℝ => Real.exp (-β * x) *
          (Real.exp (-φ * x) * W x)) (Ioi 0) := by
      simpa only [neg_mul] using hscaleInt
    have hscaleReal' :
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-β * x) * (Real.exp (-φ * x) * W x)) =
          (X.ψ (φ + β) - q)⁻¹ := by
      simpa only [neg_mul] using hscaleReal
    let fs : ℝ → ℝ := fun x =>
      Real.exp (-β * x) *
        (m * (Real.exp (-φ * x) * W x))
    have hfsInt : IntegrableOn fs (Ioi (0 : ℝ)) := by
      have htmp := hscaleInt'.const_mul m
      refine htmp.congr ?_
      filter_upwards with x
      dsimp [fs]
      ring
    have hfsPos : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fs := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hWx : 0 ≤ W x := hW.2.1 x (le_of_lt hx)
      dsimp [fs]
      positivity
    have hCDFE := positiveLaplace_cumulative_measure ν β hβ hνSupp
    have hRealFs :
        (∫ x in Ioi (0 : ℝ), fs x) =
          m * (X.ψ (φ + β) - q)⁻¹ := by
      calc
        _ = ∫ x in Ioi (0 : ℝ),
            m * (Real.exp (-β * x) *
              (Real.exp (-φ * x) * W x)) := by
              congr 1
              funext x
              dsimp [fs]
              ring
        _ = m * (∫ x in Ioi (0 : ℝ),
            Real.exp (-β * x) *
              (Real.exp (-φ * x) * W x)) := by
              rw [integral_const_mul]
        _ = _ := by rw [hscaleReal']
    have hlin :
        (∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (fs x)) =
        (∫⁻ x : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-β * x)) * ν (Iic x)) := by
      have hg : 0 < X.ψ (φ + β) - q := sub_pos.mpr hψ
      have hrat : m * (X.ψ (φ + β) - q)⁻¹ =
          (1 / β) * (m * β / (X.ψ (φ + β) - q)) := by
        field_simp [ne_of_gt hβ, ne_of_gt hg] <;> ring
      calc
        _ = ENNReal.ofReal (∫ x in Ioi (0 : ℝ), fs x) :=
              (ofReal_integral_eq_lintegral_ofReal hfsInt hfsPos).symm
        _ = ENNReal.ofReal (m * (X.ψ (φ + β) - q)⁻¹) :=
              congrArg ENNReal.ofReal hRealFs
        _ = ENNReal.ofReal ((1 / β) *
            (m * β / (X.ψ (φ + β) - q))) := by
              exact congrArg ENNReal.ofReal hrat
        _ = ENNReal.ofReal (1 / β) *
            ENNReal.ofReal (m * β / (X.ψ (φ + β) - q)) := by
              rw [ENNReal.ofReal_mul (le_of_lt (one_div_pos.mpr hβ))]
        _ = _ := by rw [← hνLap β hβ]; exact hCDFE.symm
    obtain ⟨hgin, hRealEq⟩ :=
      positive_cumulative_laplace_real_integral_bridge ν hνfin β fs hfsInt hfsPos hlin
    exact ⟨by simpa only [fs, f] using hfsInt,
      by simpa only [g] using hgin,
      by simpa only [fs, f, g] using hRealEq⟩
  have heq : ∀ x : ℝ, 0 < x → f x = g x :=
    continuous_rightContinuous_Ioi_eq_of_laplace_eq
      f g 0 hfcont hgright hgmeas hfnonneg hgnonneg
      (by intro β hβ; exact hlap β hβ)
  intro x hx
  have h := heq x hx
  dsimp [f, g] at h
  have hENN := congrArg ENNReal.ofReal h
  simpa only [neg_mul, mul_assoc, ENNReal.ofReal_toReal (hνfin x)] using hENN.symm
