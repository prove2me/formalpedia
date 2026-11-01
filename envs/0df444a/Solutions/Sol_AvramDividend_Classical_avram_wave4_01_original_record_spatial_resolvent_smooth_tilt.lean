-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_spatial_resolvent_smooth_tilt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:45:52.441983+00:00
-- url     : https://prove2.me/submissions/fab836c7-a8f7-447a-8c2e-2ab287b3b042

import Mathlib
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

/-- The genuine original first-record Esscher spatial resolvent is
C-infinity in the real tilt throughout its full admissible domain. -/
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
    ContDiffOn ℝ ⊤ (fun θ : ℝ =>
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
  have hden : ContDiffOn ℝ ⊤
      (fun θ : ℝ => θ + κ) (Ioi (-φ)) :=
    (contDiff_id.add contDiff_const).contDiffOn
  have hne : ∀ θ ∈ Ioi (-φ), θ + κ ≠ 0 := by
    intro θ hθ
    have hθpos : -φ < θ := hθ
    exact ne_of_gt (by linarith [hθpos])
  have hnum : ContDiffOn ℝ ⊤
      (fun _ : ℝ => (1 : ℝ)) (Ioi (-φ)) := contDiffOn_const
  have hfrac : ContDiffOn ℝ ⊤
      (fun θ : ℝ => (1 : ℝ) / (θ + κ)) (Ioi (-φ)) := by
    apply (hnum.div hden hne).congr
    intro θ hθ
    simp only [Pi.div_apply]
  have hinv : ContDiffOn ℝ ⊤
      (fun θ : ℝ => (θ + κ)⁻¹) (Ioi (-φ)) := by
    simpa only [one_div] using hfrac
  apply hinv.congr
  intro θ hθ
  exact avram_wave4_01_original_record_spatial_exponential_moment_resolvent
    X q hq W hW hvar φ hφ hroot a θ ha hθ
