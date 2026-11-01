-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_killed_reward_joint_height_depth_tonelli_swap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:40:24.356967+00:00
-- url     : https://prove2.me/submissions/55faec89-9a4a-49be-a7ce-9ab87e38b426

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_killed_reward_joint_height_depth_path_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- Full two-parameter Tonelli for the actual killed strict first-record reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) :
    (∫⁻ ω, ∫⁻ p in (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)),
      (if twoSidedExitUpTime X p.1 ω < barrierRuinTime X p.2 ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X p.1 ω).toReal)))
      else 0) ∂volume ∂P) =
    (∫⁻ p in (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)), ∫⁻ ω,
      (if twoSidedExitUpTime X p.1 ω < barrierRuinTime X p.2 ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X p.1 ω).toReal)))
      else 0) ∂P ∂volume) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let R : (ℝ × ℝ) → Ω → ℝ≥0∞ := fun p ω =>
    if twoSidedExitUpTime X p.1 ω < barrierRuinTime X p.2 ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X p.1 ω).toReal)))
    else 0
  have hR : Measurable (fun z : (ℝ × ℝ) × Ω => R z.1 z.2) := by
    simpa only [R] using
      (avram_wave4_01_original_killed_reward_joint_height_depth_path_measurable X q)
  have hswap := lintegral_lintegral_swap
    (μ := volume.restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))
    (ν := P) (f := R) hR.aemeasurable
  simpa only [R] using hswap.symm
