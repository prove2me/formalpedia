-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_killed_record_height_tonelli_swap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:00:26.164136+00:00
-- url     : https://prove2.me/submissions/a593dd74-486c-4bcb-9b75-fa88c695123f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_killed_record_reward_joint_height_path_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- Genuine killed first-record height-occupation reward obeys Tonelli. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a : ℝ) :
    (∫⁻ ω, ∫⁻ h in Ioi (0 : ℝ),
      (if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0) ∂volume ∂P) =
    (∫⁻ h in Ioi (0 : ℝ), ∫⁻ ω,
      (if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0) ∂P ∂volume) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let R : ℝ → Ω → ℝ≥0∞ := fun h ω =>
    if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0
  have hR : Measurable (fun p : ℝ × Ω => R p.1 p.2) := by
    simpa only [R] using
      (avram_wave4_01_original_killed_record_reward_joint_height_path_measurable X q a)
  have hswap := lintegral_lintegral_swap
    (μ := volume.restrict (Ioi (0 : ℝ))) (ν := P)
    (f := R) hR.aemeasurable
  simpa only [R] using hswap.symm
