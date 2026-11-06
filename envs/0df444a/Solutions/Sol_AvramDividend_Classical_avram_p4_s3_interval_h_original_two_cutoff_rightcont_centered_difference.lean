-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_h_original_two_cutoff_rightcont_centered_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:33:53.047205+00:00
-- url     : https://prove2.me/submissions/60905311-53f2-41db-8f9d-167344613a51

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (n : ℕ) :
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((i : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((i : ℝ) + 1))))).toReal
    let C : ℕ → Ω → ℝ := fun i ω => (N i ω).toReal - r i
    MemLp (fun ω => C n ω - C 0 ω) 2 P ∧
    (P[(fun ω => C n ω - C 0 ω) | 𝓕.rightCont s]
      =ᵐ[P] (fun _ => 0)) := by
  let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((i : ℝ) + 1))))
  let r : ℕ → ℝ := fun i =>
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((i : ℝ) + 1))))).toReal
  let C : ℕ → Ω → ℝ := fun i ω => (N i ω).toReal - r i
  change MemLp (fun ω => C n ω - C 0 ω) 2 P ∧
    (P[(fun ω => C n ω - C 0 ω) | 𝓕.rightCont s]
      =ᵐ[P] (fun _ => 0))
  have hL2 (i : ℕ) : MemLp (C i) 2 P := by
    have hOrig :=
      avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
        X (s + T) i s (s + T)
        (le_add_of_nonneg_right (zero_le : 0 ≤ T))
        le_rfl (Iic (-(1 / ((i : ℝ) + 1))))
        measurableSet_Iic (Subset.rfl)
    simpa only [C, N, r, add_tsub_cancel_left] using hOrig
  have hInt (i : ℕ) : Integrable (C i) P :=
    (hL2 i).integrable (by norm_num)
  have hCond (i : ℕ) :
      P[(C i) | 𝓕.rightCont s] =ᵐ[P] (fun _ => 0) :=
    (avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
      X s T i).1
  constructor
  · exact (hL2 n).sub (hL2 0)
  · calc
      P[(fun ω => C n ω - C 0 ω) | 𝓕.rightCont s] =ᵐ[P]
          (fun ω => (P[C n | 𝓕.rightCont s]) ω -
            (P[C 0 | 𝓕.rightCont s]) ω) := by
            exact condExp_sub (hInt n) (hInt 0) (𝓕.rightCont s)
      _ =ᵐ[P] (fun _ => 0) := by
          filter_upwards [hCond n, hCond 0] with ω hn h0
          simp only [hn, h0, sub_self]
