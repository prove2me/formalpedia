-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin_source13_original_annulus_factorial_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:21:58.192829+00:00
-- url     : https://prove2.me/submissions/842507a6-3c02-448c-ab3a-e1176c8edbdb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original negative-annulus factorial integrand is L1 from its Proved physical L2 estimate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P := by
  let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  change Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P
  have hB : MeasurableSet B := measurableSet_Ioc
  have hSep : B ⊆ Iic (-(1 / ((m : ℝ) + 1))) := by
    intro z hz
    exact hz.2
  have hL2 : MemLp (fun ω => (N ω).toReal - r) 2 P := by
    simpa only [tsub_zero] using
      (avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
        X T m 0 T (show (0 : ℝ≥0) ≤ T from zero_le) le_rfl B hB hSep)
  have hSq : Integrable (fun ω => ((N ω).toReal - r) ^ 2) P :=
    (memLp_two_iff_integrable_sq hL2.aestronglyMeasurable).1 hL2
  have hLin : Integrable (fun ω => (N ω).toReal - r) P :=
    hL2.integrable (by norm_num)
  have hEq :
      (fun ω => (N ω).toReal * ((N ω).toReal - 1)) =
      (fun ω => ((N ω).toReal - r) ^ 2 +
        (2 * r - 1) * ((N ω).toReal - r) + r * (r - 1)) := by
    funext ω
    ring
  rw [hEq]
  exact (hSq.add (hLin.const_mul _)).add (integrable_const _)