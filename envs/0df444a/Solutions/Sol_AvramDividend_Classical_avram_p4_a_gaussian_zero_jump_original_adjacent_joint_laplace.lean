-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_adjacent_joint_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:21:17.273615+00:00
-- url     : https://prove2.me/submissions/d8355aa2-b4c6-4946-b59e-6d6b91fdbafb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_adjacent_centred_increments_indep
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centred_increment_laplace

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original zero-jump Levy source has the two-parameter joint Gaussian Laplace law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (θf θp : ℝ) (hθf : 0 ≤ θf) (hθp : 0 ≤ θp) :
    (∫ ω, Real.exp
      (θf * ((Y.X u ω - Y.X t ω) - ((u - t : ℝ≥0) : ℝ) * Y.c) +
       θp * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)) ∂P) =
      Real.exp (((u - t : ℝ≥0) : ℝ) * (Y.σ ^ 2 * θf ^ 2 / 2)) *
      Real.exp (((t - s : ℝ≥0) : ℝ) * (Y.σ ^ 2 * θp ^ 2 / 2)) := by
  let Zf : Ω → ℝ := fun ω =>
    (Y.X u ω - Y.X t ω) - ((u - t : ℝ≥0) : ℝ) * Y.c
  let Zp : Ω → ℝ := fun ω =>
    (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c
  have hfMeas : Measurable Zf := by
    dsimp [Zf]
    have hu : Measurable (Y.X u) :=
      (Y.adapted u).mono (𝓕.le u) le_rfl
    have ht : Measurable (Y.X t) :=
      (Y.adapted t).mono (𝓕.le t) le_rfl
    exact (hu.sub ht).sub measurable_const
  have hpMeas : Measurable Zp := by
    dsimp [Zp]
    have ht : Measurable (Y.X t) :=
      (Y.adapted t).mono (𝓕.le t) le_rfl
    have hs : Measurable (Y.X s) :=
      (Y.adapted s).mono (𝓕.le s) le_rfl
    exact (ht.sub hs).sub measurable_const
  have hi : IndepFun Zf Zp P := by
    apply (IndepFun_iff_Indep Zf Zp P).2
    simpa only [Zf, Zp] using
      avram_p4_a_gaussian_original_adjacent_centred_increments_indep
        Y s t u hst htu
  have hθfMeas : Measurable (fun z : ℝ => θf * z) := by fun_prop
  have hθpMeas : Measurable (fun z : ℝ => θp * z) := by fun_prop
  have hscaled : IndepFun (fun ω => θf * Zf ω) (fun ω => θp * Zp ω) P := by
    simpa only [Function.comp_def] using hi.comp hθfMeas hθpMeas
  have hfac := hscaled.mgf_add' (t := 1)
    (hθfMeas.comp hfMeas).aestronglyMeasurable
    (hθpMeas.comp hpMeas).aestronglyMeasurable
  have hproduct :
      (∫ ω, Real.exp (θf * Zf ω + θp * Zp ω) ∂P) =
      (∫ ω, Real.exp (θf * Zf ω) ∂P) *
      (∫ ω, Real.exp (θp * Zp ω) ∂P) := by
    simpa only [ProbabilityTheory.mgf, Pi.add_apply, one_mul] using hfac
  calc
    _ = (∫ ω, Real.exp (θf * Zf ω) ∂P) *
          (∫ ω, Real.exp (θp * Zp ω) ∂P) := by
            simpa only [Zf, Zp] using hproduct
    _ = _ := by
      rw [show (∫ ω, Real.exp (θf * Zf ω) ∂P) =
          Real.exp (((u - t : ℝ≥0) : ℝ) * (Y.σ ^ 2 * θf ^ 2 / 2)) from by
            simpa only [Zf] using
              avram_p4_a_gaussian_zero_jump_original_centred_increment_laplace
                Y hν t u htu θf hθf]
      rw [show (∫ ω, Real.exp (θp * Zp ω) ∂P) =
          Real.exp (((t - s : ℝ≥0) : ℝ) * (Y.σ ^ 2 * θp ^ 2 / 2)) from by
            simpa only [Zp] using
              avram_p4_a_gaussian_zero_jump_original_centred_increment_laplace
                Y hν s t hst θp hθp]
