-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_annulus15_original_finite_mark_partition_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T17:37:48.760294+00:00
-- url     : https://prove2.me/submissions/8ead656e-c523-4dfd-b2a7-c98af7c0a92f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_separated_annulus_compensated_covariance_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_finite_weight_L2_of_physical_moments
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal BigOperators
noncomputable section
/-- Finite simple negative-mark source isometry for the original physical process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (k : ℕ) (cut : ℕ → ℕ) (hcut : Monotone cut) (a : ℕ → ℝ) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((cut i : ℝ) + 1))) (-(1 / ((cut (i + 1) : ℝ) + 1)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i)
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ℕ → Ω → ℝ := fun i ω => (N i ω).toReal - r i
    Integrable (fun ω => (∑ i ∈ Finset.range k, a i * Y i ω) ^ 2) P ∧
      (∫ ω, (∑ i ∈ Finset.range k, a i * Y i ω) ^ 2 ∂P) =
        ∑ i ∈ Finset.range k, (a i) ^ 2 * r i := by
  classical
  let B : ℕ → Set ℝ := fun i =>
    Ioc (-(1 / ((cut i : ℝ) + 1))) (-(1 / ((cut (i + 1) : ℝ) + 1)))
  let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B i)
  let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
  let Y : ℕ → Ω → ℝ := fun i ω => (N i ω).toReal - r i
  change Integrable (fun ω => (∑ i ∈ Finset.range k, a i * Y i ω) ^ 2) P ∧
    (∫ ω, (∑ i ∈ Finset.range k, a i * Y i ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range k, (a i) ^ 2 * r i
  apply avram_mix_annulus15_finite_weight_L2_of_physical_moments
    (Finset.range k) Y a r
  · intro i hi
    have h := avram_mixed_source13_original_physical_annulus_count_variance_exact
      X T (cut i) (cut (i + 1)) (hcut (Nat.le_succ i))
    change Integrable (fun ω => (Y i ω) ^ 2) P ∧
      (∫ ω, (Y i ω) ^ 2 ∂P) = r i at h
    exact h
  · intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have h := avram_mix_inf15_original_separated_annulus_compensated_covariance_zero
        X T (cut i) (cut (i + 1)) (cut j) (cut (j + 1))
        (hcut (Nat.le_succ i)) (hcut (Nat.succ_le_of_lt hijlt))
        (hcut (Nat.le_succ j))
      change Integrable (fun ω => Y i ω * Y j ω) P ∧
        (∫ ω, Y i ω * Y j ω ∂P) = 0 at h
      exact h
    · have h := avram_mix_inf15_original_separated_annulus_compensated_covariance_zero
        X T (cut j) (cut (j + 1)) (cut i) (cut (i + 1))
        (hcut (Nat.le_succ j)) (hcut (Nat.succ_le_of_lt hjilt))
        (hcut (Nat.le_succ i))
      change Integrable (fun ω => Y j ω * Y i ω) P ∧
        (∫ ω, Y j ω * Y i ω ∂P) = 0 at h
      constructor
      · exact h.1.congr (Filter.Eventually.of_forall
          (fun ω => mul_comm (Y j ω) (Y i ω)))
      · calc
          (∫ ω, Y i ω * Y j ω ∂P) =
              (∫ ω, Y j ω * Y i ω ∂P) := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall
                  (fun ω => mul_comm (Y i ω) (Y j ω))
          _ = 0 := h.2
