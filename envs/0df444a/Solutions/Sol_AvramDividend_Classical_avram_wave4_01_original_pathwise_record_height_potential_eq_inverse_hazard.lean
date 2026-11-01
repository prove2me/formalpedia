-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_pathwise_record_height_potential_eq_inverse_hazard
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:04:12.34769+00:00
-- url     : https://prove2.me/submissions/b673b3c9-970b-4a33-b6e4-92c90d064a49

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_killed_record_reward_joint_height_path_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_killed_record_height_tonelli_swap
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_discount_le_one
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_potential_eq_inverse_hazard
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-- The true expected pathwise killed record-height potential is inverse hazard. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a : ℝ) (ha : 0 < a) :
    (∫⁻ ω, ∫⁻ h in Ioi (0 : ℝ),
      (if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0) ∂volume ∂P).toReal =
    (deriv W a / W a)⁻¹ := by
  letI : IsProbabilityMeasure P := X.isProbability
  let R : ℝ → Ω → ℝ≥0∞ := fun h ω =>
    if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0
  have hR : Measurable (fun p : ℝ × Ω => R p.1 p.2) := by
    simpa only [R] using
      (avram_wave4_01_original_killed_record_reward_joint_height_path_measurable X q a)
  have hG : Measurable (fun h : ℝ => ∫⁻ ω, R h ω ∂P) :=
    Measurable.lintegral_prod_right hR
  have hfin (h : ℝ) : (∫⁻ ω, R h ω ∂P) < ⊤ := by
    exact lt_of_le_of_lt
      (avram_wave3_01_original_record_discount_le_one X q hq a h)
      (by simp)
  have hToReal :
      (∫ h : ℝ in Ioi 0, (∫⁻ ω, R h ω ∂P).toReal) =
      (∫⁻ h : ℝ in Ioi 0, ∫⁻ ω, R h ω ∂P).toReal := by
    exact integral_toReal hG.aemeasurable
      (Filter.Eventually.of_forall hfin)
  have hTonelli := avram_wave4_01_original_killed_record_height_tonelli_swap X q a
  have hSpatial := avram_wave4_01_original_record_spatial_potential_eq_inverse_hazard
    X q hq W hW hvar φ hφ hroot a ha
  calc
    (∫⁻ ω, ∫⁻ h in Ioi (0 : ℝ), R h ω ∂volume ∂P).toReal =
        (∫⁻ h in Ioi (0 : ℝ), ∫⁻ ω, R h ω ∂P ∂volume).toReal := by
          exact congrArg ENNReal.toReal (by simpa only [R] using hTonelli)
    _ = (∫ h : ℝ in Ioi 0, (∫⁻ ω, R h ω ∂P).toReal) := hToReal.symm
    _ = (deriv W a / W a)⁻¹ := by simpa only [R] using hSpatial
