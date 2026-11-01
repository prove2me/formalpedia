-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_discount_joint_continuity_positive_parameters
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:54:12.545891+00:00
-- url     : https://prove2.me/submissions/05fce63e-afc9-4255-a175-08f968f4c513

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_exponential_hazard
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- The actual killed discounted first-record survival is jointly continuous in positive depth and height. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        (∫⁻ ω, if twoSidedExitUpTime X p.2 ω <
            barrierRuinTime X p.1 ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X p.2 ω).toReal)))
        else 0 ∂P).toReal)
      ((Ioi (0 : ℝ)) ×ˢ (Ioi (0 : ℝ))) := by
  let K : ℝ → ℝ := fun a => -Real.log ((∫⁻ ω,
    if twoSidedExitUpTime X 1 ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P).toReal)
  let F : ℝ × ℝ → ℝ := fun p =>
    (∫⁻ ω, if twoSidedExitUpTime X p.2 ω < barrierRuinTime X p.1 ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X p.2 ω).toReal)))
    else 0 ∂P).toReal
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  have hK : ContinuousOn K (Ioi (0 : ℝ)) :=
    avram_wave3_01_original_record_log_rate_continuous
      X q hq W hW hnbv hvar
  have hK1 : ContinuousOn (fun p : ℝ × ℝ => K p.1)
      ((Ioi (0 : ℝ)) ×ˢ (Ioi (0 : ℝ))) := by
    apply hK.comp continuous_fst.continuousOn
    intro p hp
    exact hp.1
  have hh2 : ContinuousOn (fun p : ℝ × ℝ => p.2)
      ((Ioi (0 : ℝ)) ×ˢ (Ioi (0 : ℝ))) :=
    continuous_snd.continuousOn
  have hExpr : ContinuousOn (fun p : ℝ × ℝ =>
      Real.exp (-(p.2 * K p.1)))
      ((Ioi (0 : ℝ)) ×ˢ (Ioi (0 : ℝ))) :=
    Real.continuous_exp.comp_continuousOn ((hh2.mul hK1).neg)
  change ContinuousOn F ((Ioi (0 : ℝ)) ×ˢ (Ioi (0 : ℝ)))
  apply hExpr.congr
  intro p hp
  have hE := avram_wave4_01_original_record_exponential_hazard
    X q hq W hW hvar p.1 hp.1 p.2 hp.2
  change F p = Real.exp ((-p.2) * K p.1) at hE
  calc
    F p = Real.exp ((-p.2) * K p.1) := hE
    _ = Real.exp (-(p.2 * K p.1)) := by congr 1; ring
