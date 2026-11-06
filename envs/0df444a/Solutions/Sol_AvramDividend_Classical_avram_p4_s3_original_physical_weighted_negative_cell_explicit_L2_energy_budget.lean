-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_physical_weighted_negative_cell_explicit_L2_energy_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:30:54.051012+00:00
-- url     : https://prove2.me/submissions/b67fae0f-1726-4396-8d32-1db3fae3c447

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_physical_weighted_finite_band_L2_martingale_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_physical_centered_negative_cell_explicit_L2_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Explicit finite-band L² energy budget for an original bounded predictable marked jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P)
    (L : ℝ) (hBound : ∀ ω, |H ω| ≤ L) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℝ :=
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    let R : ℝ :=
      ((T : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) ≤
      L ^ 2 * (2 * (R ^ 2 + R) + 2 * r ^ 2) := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B)
  let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
  let R : ℝ := ((T : ℝ≥0∞) *
    X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
  change (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) ≤
    L ^ 2 * (2 * (R ^ 2 + R) + 2 * r ^ 2)
  have hM :=
    avram_p4_s3_original_physical_weighted_finite_band_L2_martingale_auto
      X T cut s t hst htT ε hε B hB hBand hCut H hH hHL2 L hBound
  have hB2 :=
    avram_p4_s3_original_physical_centered_negative_cell_explicit_L2_budget
      X T cut s t hst htT B hB hCut
  have hL2 : Integrable (fun ω =>
      (H ω * ((N ω).toReal - r)) ^ 2) P :=
    (memLp_two_iff_integrable_sq hM.1.aestronglyMeasurable).1 hM.1
  have hMajor : Integrable (fun ω =>
      L ^ 2 * (((N ω).toReal - r) ^ 2)) P :=
    hB2.1.const_mul _
  have hPoint (ω : Ω) :
      (H ω * ((N ω).toReal - r)) ^ 2 ≤
        L ^ 2 * (((N ω).toReal - r) ^ 2) := by
    have hl : -L ≤ H ω ∧ H ω ≤ L := by
      have hx := abs_le.mp (hBound ω)
      constructor <;> linarith
    have hs : (H ω) ^ 2 ≤ L ^ 2 := by
      have hLower : 0 ≤ L - H ω := by linarith [hl.2]
      have hUpper : 0 ≤ L + H ω := by linarith [hl.1]
      nlinarith [mul_nonneg hLower hUpper]
    calc
      (H ω * ((N ω).toReal - r)) ^ 2 =
          (H ω) ^ 2 * (((N ω).toReal - r) ^ 2) := by ring
      _ ≤ L ^ 2 * (((N ω).toReal - r) ^ 2) :=
        mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  have hI := integral_mono_ae hL2 hMajor
    (Filter.Eventually.of_forall hPoint)
  have hScale :
      (∫ ω, L ^ 2 * (((N ω).toReal - r) ^ 2) ∂P) =
      L ^ 2 * (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) := by
    simp only [integral_const_mul, smul_eq_mul]
  rw [hScale] at hI
  exact hI.trans (mul_le_mul_of_nonneg_left hB2.2 (sq_nonneg L))
