-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_annulus14_original_shifted_fullcutoff_factorial_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:11:30.310282+00:00
-- url     : https://prove2.me/submissions/b4ff92b5-5458-465e-9ebd-dc30348561f3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_band_count_factorial_moment_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact factorial moment of the original full-cutoff count in a shifted physical cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (m : ℕ) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((m : ℝ) + 1))))
    let r : ℝ := ((T : ℝ≥0∞) *
      X.ν (Iic (-(1 / ((m : ℝ) + 1))))).toReal
    Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
      (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2 := by
  let B : Set ℝ := Iic (-(1 / ((m : ℝ) + 1)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let N₀ : Ω → ℝ≥0∞ := fun ω => NX ω (Ioc 0 T ×ˢ B)
  let N : Ω → ℝ≥0∞ := fun ω => NX ω (Ioc s (s + T) ×ˢ B)
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  let g : ℝ≥0∞ → ℝ := fun z => z.toReal * (z.toReal - 1)
  change Integrable (fun ω => g (N ω)) P ∧
    (∫ ω, g (N ω) ∂P) = r ^ 2
  have hOrigin := avram_p4_f2_original_band_count_factorial_moment_exact X T m
  change Integrable (fun ω => g (N₀ ω)) P ∧
    (∫ ω, g (N₀ ω) ∂P) = r ^ 2 at hOrigin
  have hg : Measurable g := by
    dsimp [g]
    exact ENNReal.measurable_toReal.mul
      (ENNReal.measurable_toReal.sub measurable_const)
  have hStationary :=
    avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
      X NX (by intro ω; rfl) s T B measurableSet_Iic g hg hOrigin.1
  change Integrable (fun ω => g (N ω)) P ∧
    (∫ ω, g (N ω) ∂P) =
      (∫ ω, g (N₀ ω) ∂P) at hStationary
  exact ⟨hStationary.1, hStationary.2.trans hOrigin.2⟩
