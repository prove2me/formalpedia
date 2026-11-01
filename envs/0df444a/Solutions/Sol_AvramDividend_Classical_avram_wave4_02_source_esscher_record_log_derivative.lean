-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_source_esscher_record_log_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:07:34.72476+00:00
-- url     : https://prove2.me/submissions/6188aed8-04e4-4fc0-a3ed-59ef0f723062

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_canonical_infinite_jump_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_genuine_local_scale_ratio_sandwich
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_local_exponential_scale_sandwich_log_deriv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

/-- The source killed-first-record height rate is exactly the log derivative
of the actual Esscher-tilted scale, with the positive-root shift. -/
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
    (a : ℝ) (ha : 0 < a) :
    HasDerivAt (fun z : ℝ => Real.log (V z))
      (-Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
        barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
      else 0 ∂P).toReal) - φ) a := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun d h =>
    ∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X d ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P
  let κ : ℝ → ℝ := fun d => -Real.log ((F d 1).toReal)
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  have hWpos : ∀ d : ℝ, 0 < d → 0 < W d := by
    intro d hd
    exact scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv d hd
  have hκ : ContinuousOn κ (Ioi (0 : ℝ)) := by
    simpa only [κ, F] using
      (avram_wave3_01_canonical_infinite_jump_log_rate_continuous
        X q hq W hW hvar)
  have hFdef : ∀ d h : ℝ, F d h =
      ∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X d ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P := by intros; rfl
  have hκdef : ∀ d : ℝ, κ d = -Real.log ((F d 1).toReal) := by
    intro d
    rfl
  have hsand := avram_wave4_01_genuine_local_scale_ratio_sandwich
    X q hq W hW hvar F hFdef κ hκdef
  have hlogW := avram_wave4_01_local_exponential_scale_sandwich_log_deriv
    W κ hWpos hκ hsand
  change HasDerivAt (fun z : ℝ => Real.log (V z)) (κ a - φ) a
  have hlinear : HasDerivAt (fun z : ℝ => φ * z) φ a := by
    exact hasDerivAt_const_mul φ
  have hD : HasDerivAt
      (fun z : ℝ => Real.log (W z) - φ * z) (κ a - φ) a :=
    (hlogW a ha).sub hlinear
  have heq : (fun z : ℝ => Real.log (V z)) =ᶠ[𝓝 a]
      (fun z : ℝ => Real.log (W z) - φ * z) := by
    filter_upwards [isOpen_Ioi.mem_nhds ha] with z hz
    rw [hV z hz, Real.log_mul (Real.exp_ne_zero _)
      (ne_of_gt (hWpos z hz)), Real.log_exp]
    ring
  exact hD.congr_of_eventuallyEq heq
