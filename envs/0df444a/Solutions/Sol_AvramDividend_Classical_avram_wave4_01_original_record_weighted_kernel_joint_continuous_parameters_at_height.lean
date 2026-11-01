-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_weighted_kernel_joint_continuous_parameters_at_height
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:19:19.799017+00:00
-- url     : https://prove2.me/submissions/c439f3e5-c07e-4b81-b191-69f02b0367a6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_survival_joint_continuous_height_depth
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

/-- Genuine first-record Esscher kernels are pointwise joint-continuous in tilt and depth. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ h : ℝ) (hh : 0 < h) :
    ContinuousOn (fun p : ℝ × ℝ =>
      Real.exp (-(p.1 * h)) *
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
            barrierRuinTime X p.2 ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal)
      ((Ioi (-φ)).prod (Ioi (0 : ℝ))) := by
  let U : Set (ℝ × ℝ) := (Ioi (-φ)).prod (Ioi (0 : ℝ))
  have hsource :=
    avram_wave4_01_original_record_survival_joint_continuous_height_depth
      X q hq W hW hvar
  have hpair : ContinuousOn (fun p : ℝ × ℝ => (h, p.2)) U :=
    (continuous_const.prodMk continuous_snd).continuousOn
  have hG : ContinuousOn (fun p : ℝ × ℝ =>
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
                  barrierRuinTime X p.2 ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal) U := by
    simpa only [Function.comp_def] using
      (hsource.comp hpair (by
        intro p hp
        exact ⟨hh, hp.2⟩))
  have harg : Continuous (fun p : ℝ × ℝ => -(p.1 * h)) :=
    (continuous_fst.mul continuous_const).neg
  have he : ContinuousOn (fun p : ℝ × ℝ =>
      Real.exp (-(p.1 * h))) U :=
    (Real.continuous_exp.comp harg).continuousOn
  exact he.mul hG
