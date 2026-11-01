-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_discount_attains_subunrestricted_level
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:54:30.728786+00:00
-- url     : https://prove2.me/submissions/c3413ac8-bef6-4989-95a3-7354563a7c49

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_exponential_hazard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_tendsto_zero_depth
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_depth_tendsto_unrestricted_root
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-- Calibrate the actual killed first-record discounted survival to any subunrestricted target. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (h : ℝ) (hh : 0 < h)
    (r : ℝ) (hr0 : 0 < r) (hr : r < Real.exp (-(h * φ))) :
    ∃ a : ℝ, 0 < a ∧
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal = r := by
  let F : ℝ → ℝ := fun a =>
    (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P).toReal
  let K : ℝ → ℝ := fun a => -Real.log ((∫⁻ ω,
    if twoSidedExitUpTime X 1 ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P).toReal)
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  have hKcont : ContinuousOn K (Ioi (0 : ℝ)) :=
    avram_wave3_01_original_record_log_rate_continuous
      X q hq W hW hnbv hvar
  have hexp : ContinuousOn (fun a => Real.exp (-(h * K a))) (Ioi (0 : ℝ)) := by
    exact Real.continuous_exp.comp_continuousOn
      ((continuousOn_const.mul hKcont).neg)
  have hFcont : ContinuousOn F (Ioi (0 : ℝ)) := by
    apply hexp.congr
    intro a ha
    have hE := avram_wave4_01_original_record_exponential_hazard
      X q hq W hW hvar a ha h hh
    change F a = Real.exp ((-h) * K a) at hE
    calc
      F a = Real.exp ((-h) * K a) := hE
      _ = Real.exp (-(h * K a)) := by congr 1; ring
  have hzero : Tendsto F (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 : ℝ)) :=
    avram_wave4_01_original_record_discount_tendsto_zero_depth
      X q hq W hW hvar h hh
  have hinfty : Tendsto F atTop (nhds (Real.exp (-(h * φ)))) :=
    avram_wave4_01_original_record_discount_depth_tendsto_unrestricted_root
      X q hq W hW hvar φ hφ hroot h hh
  have hnear : ∀ᶠ a : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      0 < a ∧ a < 1 ∧ F a < r := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds (0 : ℝ)),
      hzero.eventually (eventually_lt_nhds hr0)] with a ha ha1 hFr
    exact ⟨ha, ha1, hFr⟩
  obtain ⟨a, ha, ha1, haF⟩ := hnear.exists
  have hfar : ∀ᶠ b : ℝ in atTop, 1 ≤ b ∧ r < F b := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      hinfty.eventually (eventually_gt_nhds hr)] with b hb hbF
    exact ⟨hb, hbF⟩
  obtain ⟨b, hb, hbF⟩ := hfar.exists
  have hab : a ≤ b := by linarith
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := by
    intro z hz
    exact lt_of_lt_of_le ha hz.1
  have hval : r ∈ Icc (F a) (F b) := ⟨le_of_lt haF, le_of_lt hbF⟩
  obtain ⟨c, hc, hceq⟩ :=
    (intermediate_value_Icc hab (hFcont.mono hsub)) hval
  exact ⟨c, lt_of_lt_of_le ha hc.1, hceq⟩
