-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_original_reciprocal_band_count_L1_Campbell_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:08:58.140799+00:00
-- url     : https://prove2.me/submissions/8c65f602-869f-4471-b1f6-a78b30746a9e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_finite_negative_band_facts
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anynu_finite_negative_Borel_weighted_past_compensator_real_L1
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n m : ℕ) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let N : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ B)).toReal
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable N P ∧ (∫ ω, N ω ∂P) = r := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let B : Set ℝ :=
    Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  obtain ⟨hBm, hNeg, hν⟩ :=
    avram_twoagentA_shared_original_finite_negative_band_facts X n m
  have hCampbell :=
    avram_jump6_B_original_anynu_finite_negative_Borel_weighted_past_compensator_real_L1
      X 0 T (by positivity) B hBm
      (fun _ : Ω => (1 : ℝ≥0∞)) (fun _ : Ω => (0 : ℝ≥0∞))
      measurable_const measurable_const
      (by simp) (by simp) hν hNeg
  simpa [B, zero_mul, one_mul] using hCampbell
