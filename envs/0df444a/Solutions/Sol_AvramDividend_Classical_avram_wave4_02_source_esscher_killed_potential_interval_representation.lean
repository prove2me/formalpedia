-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_source_esscher_killed_potential_interval_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:22:46.149114+00:00
-- url     : https://prove2.me/submissions/5199acd6-e348-4115-8992-3c56912bf0dd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_height_rate_nonneg_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_log_derivative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

/-- Exact original-source killed-record potential representation for the
actual tilted q-scale: the rate is a real stopped-record expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ z : ℝ, 0 < z → V z = Real.exp (-(φ * z)) * W z)
    (x a : ℝ) (hx : 0 < x) (hxa : x ≤ a) :
    V x / V a =
      Real.exp (-(∫ t in x..a,
        (-Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
          barrierRuinTime X t ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal) - φ))) := by
  let rate : ℝ → ℝ := fun t =>
    -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
      barrierRuinTime X t ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P).toReal) - φ
  change V x / V a = Real.exp (-(∫ t in x..a, rate t))
  have ha : 0 < a := lt_of_lt_of_le hx hxa
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  have hWpos : ∀ t : ℝ, 0 < t → 0 < W t := by
    intro t ht
    exact scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv t ht
  have hVpos : ∀ t : ℝ, 0 < t → 0 < V t := by
    intro t ht
    rw [hV t ht]
    exact mul_pos (Real.exp_pos _) (hWpos t ht)
  have hratecont : ContinuousOn rate (Ioi (0 : ℝ)) := by
    change ContinuousOn
      (fun t : ℝ =>
        -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
          barrierRuinTime X t ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal) - φ) (Ioi (0 : ℝ))
    exact (avram_wave4_02_source_esscher_record_height_rate_nonneg_continuous
      X q hq W hW hvar φ hφ hroot).1
  have hsub : Icc x a ⊆ Ioi (0 : ℝ) := by
    intro t ht
    exact lt_of_lt_of_le hx ht.1
  have hrateint : IntervalIntegrable rate MeasureTheory.volume x a := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hxa] using hratecont.mono hsub
  have hD : ∀ t ∈ Ioo x a,
      HasDerivAt (fun z : ℝ => Real.log (V z)) (rate t) t := by
    intro t ht
    have htpos : 0 < t := lt_trans hx ht.1
    exact avram_wave4_02_source_esscher_record_log_derivative
      X q hq W hW hvar φ hφ hroot V hV t htpos
  have hCont : ContinuousOn (fun z : ℝ => Real.log (V z)) (Icc x a) := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hx ht.1
    exact (avram_wave4_02_source_esscher_record_log_derivative
      X q hq W hW hvar φ hφ hroot V hV t htpos).continuousAt.continuousWithinAt
  have hFTC : ∫ t in x..a, rate t = Real.log (V a) - Real.log (V x) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxa hCont hD hrateint
  calc
    V x / V a = Real.exp (Real.log (V x / V a)) :=
      (Real.exp_log (div_pos (hVpos x hx) (hVpos a ha))).symm
    _ = Real.exp (Real.log (V x) - Real.log (V a)) := by
      rw [Real.log_div (ne_of_gt (hVpos x hx)) (ne_of_gt (hVpos a ha))]
    _ = Real.exp (-(∫ t in x..a, rate t)) := by rw [hFTC]; congr 1; ring
