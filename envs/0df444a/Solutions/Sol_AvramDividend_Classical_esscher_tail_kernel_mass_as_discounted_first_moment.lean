-- Prove2me | solution 1 for AvramDividend.Classical.esscher_tail_kernel_mass_as_discounted_first_moment
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:18:25.387043+00:00
-- url     : https://prove2.me/submissions/8f4be362-62a1-4ee4-8a8d-5f385197a37c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (μ : Measure ℝ≥0) (φ : ℝ) :
    let μφ : Measure ℝ≥0 :=
      μ.withDensity (fun z : ℝ≥0 =>
        ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))
    let κφ : Measure ℝ :=
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t : ℝ => μφ {z : ℝ≥0 | t < (z : ℝ)})
    κφ Set.univ =
      ∫⁻ z : ℝ≥0,
        ENNReal.ofReal ((z : ℝ) * Real.exp (-(φ * (z : ℝ)))) ∂μ := by
  let μφ : Measure ℝ≥0 :=
    μ.withDensity (fun z : ℝ≥0 =>
      ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))
  let κφ : Measure ℝ :=
    (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun t : ℝ => μφ {z : ℝ≥0 | t < (z : ℝ)})
  have hf : Measurable
      (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))) := by
    fun_prop
  have hg : Measurable
      (fun z : ℝ≥0 => ENNReal.ofReal (z : ℝ)) := by
    fun_prop
  change κφ Set.univ =
    ∫⁻ z : ℝ≥0,
      ENNReal.ofReal ((z : ℝ) * Real.exp (-(φ * (z : ℝ)))) ∂μ
  calc
    κφ Set.univ =
      (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μφ) :=
        positive_jump_tail_density_total_mass μφ
    _ = (∫⁻ z : ℝ≥0,
      ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
        ENNReal.ofReal (z : ℝ) ∂μ) := by
          exact lintegral_withDensity_eq_lintegral_mul μ hf hg
    _ = ∫⁻ z : ℝ≥0,
      ENNReal.ofReal ((z : ℝ) * Real.exp (-(φ * (z : ℝ)))) ∂μ := by
        apply lintegral_congr
        intro z
        rw [ENNReal.ofReal_mul (NNReal.coe_nonneg z)]
        ac_rfl
