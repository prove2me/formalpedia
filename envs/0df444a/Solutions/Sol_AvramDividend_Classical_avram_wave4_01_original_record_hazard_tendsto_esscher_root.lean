-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_hazard_tendsto_esscher_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:38:41.186403+00:00
-- url     : https://prove2.me/submissions/9e55214f-cb56-499e-94fa-7a076976789d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_infinite_variation_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_positive_monotone_of_given_root
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_hazard_antitone_depth
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_log_derivative
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_log_derivative_flatness
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_source_esscher_flatness_to_record_hazard_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-- Genuine reflected first-record hazard approaches the unrestricted root. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    Tendsto
      (fun a : ℝ => -Real.log
        ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                    barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
          else 0 ∂P).toReal))
      atTop (nhds φ) := by
  let V : ℝ → ℝ := fun z => Real.exp (-(φ * z)) * W z
  let K : ℝ → ℝ := fun a => -Real.log ((∫⁻ ω,
    if twoSidedExitUpTime X 1 ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P).toReal)
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  have hC1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_infinite_variation_without_standing X q hq W hW hvar
  have hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x := by intros; rfl
  have hVpos : ∀ x : ℝ, 0 < x → 0 < V x := by
    intro x hx
    exact mul_pos (Real.exp_pos _)
      (scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv x hx)
  have hVdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ V x := by
    intro x hx
    change DifferentiableAt ℝ (fun z : ℝ => Real.exp (-(φ * z)) * W z) x
    have hinner : DifferentiableAt ℝ (fun z : ℝ => -(φ * z)) x := by fun_prop
    exact (Real.differentiableAt_exp.comp x hinner).mul
      ((hC1.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt (by norm_num))
  have htilt : MonotoneOn V (Ioi (0 : ℝ)) := by
    simpa only [V, neg_mul] using
      (unbounded_tilted_positive_monotone_of_given_root X q hq W hW hnbv φ hφ hroot)
  have hKanti : AntitoneOn K (Ioi (0 : ℝ)) :=
    avram_wave4_01_original_record_log_hazard_antitone_depth X q hq W hW hnbv
  have hD : ∀ x : ℝ, 0 < x →
      deriv (fun z : ℝ => Real.log (V z)) x = K x - φ := by
    intro x hx
    exact (avram_wave4_02_source_esscher_record_log_derivative
      X q hq W hW hvar φ hφ hroot V hV x hx).deriv
  have hanti : AntitoneOn
      (fun x : ℝ => deriv (fun z : ℝ => Real.log (V z)) x)
      (Ioi (0 : ℝ)) := by
    intro a ha b hb hab
    change deriv (fun z : ℝ => Real.log (V z)) b ≤ deriv (fun z : ℝ => Real.log (V z)) a
    rw [hD b hb, hD a ha]
    exact sub_le_sub_right (hKanti ha hb hab) φ
  have hflat : Tendsto
      (fun x : ℝ => deriv (fun y : ℝ => Real.log (V y)) x)
      atTop (nhds (0 : ℝ)) :=
    unbounded_esscher_log_derivative_flatness
      X q hq W hW hnbv φ hφ hroot V hV hVpos hVdiff htilt hanti
  exact avram_wave4_01_source_esscher_flatness_to_record_hazard_limit
    X q hq W hW hvar φ hφ hroot V hV hflat
