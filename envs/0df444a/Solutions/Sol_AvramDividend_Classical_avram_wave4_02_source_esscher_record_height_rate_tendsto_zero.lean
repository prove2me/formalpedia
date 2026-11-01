-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_source_esscher_record_height_rate_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:28:17.895337+00:00
-- url     : https://prove2.me/submissions/616e7729-677c-43ba-acd4-924439c17dc2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_C1_of_infinite_small_jump_without_standing
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_positive_monotone_of_given_root
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_log_derivative_flatness
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_log_derivative
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_height_rate_antitone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

/-- The actual killed-record Esscher excess height rate has no persistent
mass at arbitrarily large barriers; source-identified, no Itô PPP assumed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    Tendsto (fun a : ℝ =>
      -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
        barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
      else 0 ∂P).toReal) - φ) atTop (nhds (0 : ℝ)) := by
  let V : ℝ → ℝ := fun z => Real.exp (-(φ * z)) * W z
  let rate : ℝ → ℝ := fun a =>
    -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
      barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P).toReal) - φ
  change Tendsto rate atTop (nhds (0 : ℝ))
  have hV : ∀ z : ℝ, 0 < z →
      V z = Real.exp (-(φ * z)) * W z := by intros; rfl
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  have hVpos : ∀ z : ℝ, 0 < z → 0 < V z := by
    intro z hz
    exact mul_pos (Real.exp_pos _)
      (scaleFunction_strict_pos_of_unbounded_variation
        X q W hW hnbv z hz)
  have hC1 : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) :=
    esscher_tilted_scale_C1_of_infinite_small_jump_without_standing
      X q hq W hW hvar φ hφ hroot V hV
  have hVdiff : ∀ z : ℝ, 0 < z → DifferentiableAt ℝ V z := by
    intro z hz
    exact (hC1.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  have htilt : MonotoneOn V (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    rw [hV x hx, hV y hy]
    simpa only [neg_mul] using
      (unbounded_tilted_positive_monotone_of_given_root
        X q hq W hW hnbv φ hφ hroot hx hy hxy)
  have hD : ∀ a : ℝ, 0 < a →
      deriv (fun z : ℝ => Real.log (V z)) a = rate a := by
    intro a ha
    exact (avram_wave4_02_source_esscher_record_log_derivative
      X q hq W hW hvar φ hφ hroot V hV a ha).deriv
  have hanti : AntitoneOn
      (fun a : ℝ => deriv (fun z : ℝ => Real.log (V z)) a)
      (Ioi (0 : ℝ)) := by
    intro a ha b hb hab
    calc
      deriv (fun z : ℝ => Real.log (V z)) b = rate b := hD b hb
      _ ≤ rate a :=
        avram_wave4_02_source_esscher_record_height_rate_antitone
          X q hq W hW hvar φ hφ hroot a b ha hab
      _ = deriv (fun z : ℝ => Real.log (V z)) a := (hD a ha).symm
  have hflat : Tendsto
      (fun a : ℝ => deriv (fun z : ℝ => Real.log (V z)) a)
      atTop (nhds (0 : ℝ)) :=
    unbounded_esscher_log_derivative_flatness
      X q hq W hW hnbv φ hφ hroot V hV hVpos hVdiff htilt hanti
  have heq : (fun a : ℝ =>
      deriv (fun z : ℝ => Real.log (V z)) a) =ᶠ[atTop] rate := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    exact hD a ha
  exact hflat.congr' heq
