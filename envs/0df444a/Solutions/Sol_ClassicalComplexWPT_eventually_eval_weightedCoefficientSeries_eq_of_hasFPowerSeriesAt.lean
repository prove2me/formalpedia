-- Prove2me | solution 1 for ClassicalComplexWPT.eventually_eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:13:54.795842+00:00
-- url     : https://prove2.me/submissions/227d54b9-b3be-429c-8b7e-bd9faa43e346

import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Theorems.Thm_ClassicalComplexWPT_ambient_zero_eq
import Theorems.Thm_ClassicalComplexWPT_eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesOnBall
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_radius_weightedCoefficientSeries_pos
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero
attribute [local simp] ClassicalComplexWPT.weightedLastCoeffs_apply



set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution
    {n : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hp : HasFPowerSeriesAt f p 0) (hr0 : 0 < r)
    (hrp : (r : ℝ≥0∞) < p.radius) :
    (fun x : Ambient n ↦
      evalL1PowerSeries ((weightedCoefficientSeries p r).sum x.1)
        ((r : ℂ)⁻¹ * x.2)) =ᶠ[𝓝 0] f := by
  obtain ⟨ρ, hpρ⟩ := hp
  have hzq : ∀ᶠ x : Ambient n in 𝓝 0,
      x.1 ∈ Metric.eball (0 : Base n) (weightedCoefficientSeries p r).radius := by
    have hball := Metric.eball_mem_nhds (0 : Base n)
      (radius_weightedCoefficientSeries_pos p r hrp)
    exact continuousAt_fst.eventually hball
  have hzw : ∀ᶠ x : Ambient n in 𝓝 0,
      (‖(x.1, (0 : ℂ))‖₊ + ‖((0 : Base n), x.2)‖₊ : ℝ≥0∞) < ρ := by
    let s : Ambient n → ℝ≥0∞ := fun x ↦
      (‖(x.1, (0 : ℂ))‖₊ : ℝ≥0∞) +
        (‖((0 : Base n), x.2)‖₊ : ℝ≥0∞)
    have hs : ContinuousAt s 0 := by
      dsimp only [s]
      fun_prop
    have hopen : Set.Iio ρ ∈ 𝓝 (s 0) := by
      apply Iio_mem_nhds
      simpa [s, ambient_zero_eq] using hpρ.r_pos
    simpa only [s] using hs.eventually hopen
  have hw : ∀ᶠ x : Ambient n in 𝓝 0, ‖x.2‖ < r := by
    have hball := Metric.ball_mem_nhds (0 : ℂ) (by exact_mod_cast hr0)
    have hsnd : ∀ᶠ x : Ambient n in 𝓝 0, x.2 ∈ Metric.ball (0 : ℂ) (r : ℝ) :=
      continuousAt_snd.eventually hball
    simpa only [Metric.mem_ball, dist_zero_right] using hsnd
  filter_upwards [hzq, hzw, hw] with x hxq hxρ hxw
  exact eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesOnBall
    p r hpρ hr0 hrp x.1 x.2 hxq hxρ hxw
end ClassicalComplexWPT
