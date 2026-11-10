-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_annulus16_original_shifted_physical_variance_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:03:57.574765+00:00
-- url     : https://prove2.me/submissions/faa13d9b-1ed4-45b3-a1f4-808d4c403de2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => ((N ω).toReal - r) ^ 2) P ∧
      (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) = r := by
  dsimp only
  let B : Set ℝ :=
    Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  have hBase :=
    avram_mixed_source13_original_physical_annulus_count_variance_exact
      X T n m hnm
  rcases hBase with ⟨hI, hEq⟩
  have hB : MeasurableSet B := by
    dsimp [B]
    exact measurableSet_Ioc
  have hg : Measurable (fun z : ℝ≥0∞ => (z.toReal - r) ^ 2) := by
    fun_prop
  have hStat :=
    avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
      X NX (by intro ω; rfl) s T B hB
      (fun z : ℝ≥0∞ => (z.toReal - r) ^ 2) hg
      (by simpa [NX, B, r] using hI)
  constructor
  · simpa [NX, B, r] using hStat.1
  · calc
      (∫ ω, ((NX ω (Ioc s (s + T) ×ˢ B)).toReal - r) ^ 2 ∂P)
          = ∫ ω, ((NX ω (Ioc 0 T ×ˢ B)).toReal - r) ^ 2 ∂P :=
              hStat.2
      _ = r := by simpa [NX, B, r] using hEq
