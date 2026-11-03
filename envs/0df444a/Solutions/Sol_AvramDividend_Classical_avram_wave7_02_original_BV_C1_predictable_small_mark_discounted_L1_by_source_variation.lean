-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_C1_predictable_small_mark_discounted_L1_by_source_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:21:49.006525+00:00
-- url     : https://prove2.me/submissions/0b6145be-d03e-4744-bc8a-e59013497987

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original controlled predictable C1 small negative marks have a
discounted absolute bound by genuine source variation on an interior strip. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (a b L : ℝ) (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (ω : Ω) (t : ℝ≥0)
    (hBand : Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t ∈ Icc a b)
    (z : ℝ) (hzSmall : -a / 2 ≤ z ∧ z ≤ 0) :
    |Real.exp (-(q * (t : ℝ))) *
      (w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t + z) -
      w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t))| ≤ L * |z| := by
  let y : ℝ := Function.leftLim (fun s : ℝ≥0 =>
    x + X.X s ω - rightLimit D s ω) t
  change |Real.exp (-(q * (t : ℝ))) * (w (y + z) - w y)| ≤ L * |z|
  change y ∈ Icc a b at hBand
  have hy : y ∈ Icc (a / 2) b := ⟨by linarith only [hBand.1, ha], hBand.2⟩
  have hyz : y + z ∈ Icc (a / 2) b := by
    constructor
    · linarith [hBand.1, hzSmall.1]
    · linarith [hBand.2, hzSmall.2]
  have hBound := hLip (y + z) hyz y hy
  have hDelta : |(y + z) - y| = |z| := by ring
  rw [hDelta] at hBound
  have hTime : 0 ≤ (t : ℝ) := NNReal.coe_nonneg _
  have hexp : Real.exp (-(q * (t : ℝ))) ≤ 1 := by
    have hneg : -(q * (t : ℝ)) ≤ 0 := neg_nonpos.mpr (mul_nonneg hq hTime)
    simpa using (Real.exp_le_exp.mpr hneg)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-(q * (t : ℝ))) * |w (y + z) - w y|
        ≤ Real.exp (-(q * (t : ℝ))) * (L * |z|) :=
          mul_le_mul_of_nonneg_left hBound (Real.exp_pos _).le
    _ ≤ 1 * (L * |z|) :=
      mul_le_mul_of_nonneg_right hexp (mul_nonneg hL (abs_nonneg _))
    _ = L * |z| := one_mul _
