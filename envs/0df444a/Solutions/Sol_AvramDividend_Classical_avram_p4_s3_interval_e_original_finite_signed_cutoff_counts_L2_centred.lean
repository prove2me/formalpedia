-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_e_original_finite_signed_cutoff_counts_L2_centred
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:18:39.969337+00:00
-- url     : https://prove2.me/submissions/ecef5e83-85d2-4ff7-b9e1-a79ea013850c

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite deterministic signed cutoff sums of the *original* intrinsic jump counts are centred L² variables. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n : ι → ℕ) (a : ι → ℝ) (F : Finset ι) :
    let B : ι → Set ℝ := fun i => Iic (-(1 / (((n i : ℕ) : ℝ) + 1)))
    let N : ι → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i)
    let r : ι → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let Z : ι → Ω → ℝ := fun i ω => a i * ((N i ω).toReal - r i)
    MemLp (∑ i ∈ F, Z i) 2 P ∧
      (∫ ω, ∑ i ∈ F, Z i ω ∂P) = 0 := by
  classical
  let B : ι → Set ℝ := fun i => Iic (-(1 / (((n i : ℕ) : ℝ) + 1)))
  let N : ι → Ω → ℝ≥0∞ := fun i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B i)
  let r : ι → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
  let Z : ι → Ω → ℝ := fun i ω => a i * ((N i ω).toReal - r i)
  change MemLp (∑ i ∈ F, Z i) 2 P ∧
    (∫ ω, ∑ i ∈ F, Z i ω ∂P) = 0
  have hCell (i : ι) : MemLp (fun ω => (N i ω).toReal - r i) 2 P := by
    simpa only [tsub_zero] using
      (avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
        X T (n i) 0 T (show (0 : ℝ≥0) ≤ T from zero_le)
          le_rfl (B i) measurableSet_Iic (Subset.rfl))
  have hZ (i : ι) : MemLp (Z i) 2 P := by
    simpa only [Z] using (hCell i).const_mul (a i)
  have hZMean (i : ι) : (∫ ω, Z i ω ∂P) = 0 := by
    have hCountInt : Integrable (fun ω => (N i ω).toReal) P := by
      have h := ((hCell i).integrable (by norm_num)).add
        (integrable_const (r i))
      exact h.congr (Filter.Eventually.of_forall (fun ω => by simp [Pi.add_apply]))
    have hRawMean : (∫ ω, (N i ω).toReal ∂P) = r i :=
      avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto
        X T (n i)
    have hCentered : (∫ ω, (N i ω).toReal - r i ∂P) = 0 := by
      rw [integral_sub hCountInt (integrable_const _), hRawMean]
      simp
    change (∫ ω, a i * ((N i ω).toReal - r i) ∂P) = 0
    rw [integral_const_mul, hCentered]
    simp
  constructor
  · induction F using Finset.induction_on with
    | empty => simp
    | @insert b S hb ih =>
      simpa only [Finset.sum_insert hb] using ((hZ b).add ih)
  · rw [integral_finset_sum F (by
      intro i hi
      exact (hZ i).integrable (by norm_num))]
    simp only [hZMean, Finset.sum_const_zero]
