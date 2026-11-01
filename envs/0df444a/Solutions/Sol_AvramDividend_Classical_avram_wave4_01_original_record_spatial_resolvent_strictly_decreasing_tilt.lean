-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_spatial_resolvent_strictly_decreasing_tilt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:51:19.827602+00:00
-- url     : https://prove2.me/submissions/7bdd3945-0459-4c7f-8482-84d781023073

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_exponential_moment_resolvent
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- The genuine original-process first-record height potential decreases
strictly as its admissible real Esscher spatial tilt grows. -/
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
    StrictAntiOn (fun θ : ℝ =>
      ∫ h : ℝ in Ioi 0,
        Real.exp (-(θ * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal) (Ioi (-φ)) := by
  let κ : ℝ := deriv W a / W a
  have hκ : φ ≤ κ :=
    avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
      X q hq W hW hvar φ hφ hroot a ha
  intro θ₁ hθ₁ θ₂ hθ₂ hlt
  have ht1 : -φ < θ₁ := hθ₁
  have ht2 : -φ < θ₂ := hθ₂
  have hp1 : 0 < θ₁ + κ := by linarith [ht1]
  have hp2 : 0 < θ₂ + κ := by linarith [ht2]
  have hfrac : 1 / (θ₂ + κ) < 1 / (θ₁ + κ) :=
    (one_div_lt_one_div hp2 hp1).2 (by linarith)
  dsimp only
  rw [avram_wave4_01_original_record_spatial_exponential_moment_resolvent
      X q hq W hW hvar φ hφ hroot a θ₂ ha hθ₂,
    avram_wave4_01_original_record_spatial_exponential_moment_resolvent
      X q hq W hW hvar φ hφ hroot a θ₁ ha hθ₁]
  simpa only [one_div, κ] using hfrac
