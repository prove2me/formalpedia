-- Prove2me | solution 1 for DistInterpRO.Consistency.kde_mem_distSet
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:41:59.548665+00:00
-- url     : https://prove2.me/submissions/4beda735-79e4-43cb-8904-b9fef82dbf04

import Mathlib
import Definitions.Def_DistInterpRO_Consistency_Model

open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Consistency

theorem aux_kdeds_density {m n : ℕ} {ε : ℝ} (hε : 0 < ε) (xs : Fin n → Fin m → ℝ) :
    (fun x => ENNReal.ofReal (kde ε xs x)) = fun x => ∑ i : Fin n,
      (box (xs i) ε).indicator (fun _ => ENNReal.ofReal (((n : ℝ) * ε ^ m)⁻¹ * (1 / (2 : ℝ) ^ m))) x := by
  funext x
  unfold kde
  have hnn : (0 : ℝ) ≤ ((n : ℝ) * ε ^ m)⁻¹ := by positivity
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    have hiff : ‖ε⁻¹ • (x - xs i)‖ ≤ 1 ↔ x ∈ box (xs i) ε := by
      rw [box, Metric.mem_closedBall, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hε, inv_mul_le_iff₀ hε, mul_one]
    unfold kernel
    by_cases h : x ∈ box (xs i) ε
    · rw [if_pos (hiff.mpr h), Set.indicator_of_mem h]
    · rw [if_neg (fun h' => h (hiff.mp h')), Set.indicator_of_notMem h, mul_zero,
        ENNReal.ofReal_zero]
  · intro i _
    unfold kernel
    split_ifs <;> positivity

theorem aux_kdeds_mass {m n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (xi : Fin m → ℝ) :
    ENNReal.ofReal (((n : ℝ) * ε ^ m)⁻¹ * (1 / (2 : ℝ) ^ m)) * volume (box xi ε)
      = ENNReal.ofReal (1 / (n : ℝ)) := by
  rw [box, Real.volume_pi_closedBall xi hε.le, Fintype.card_fin, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mul_pow]
  field_simp

theorem aux_kdeds_apply {m n : ℕ} {ε : ℝ} (hε : 0 < ε) (xs : Fin n → Fin m → ℝ)
    (A : Set (Fin m → ℝ)) (hA : MeasurableSet A) :
    volume.withDensity (fun x => ENNReal.ofReal (kde ε xs x)) A
      = ∑ i : Fin n, ENNReal.ofReal (((n : ℝ) * ε ^ m)⁻¹ * (1 / (2 : ℝ) ^ m))
          * volume (box (xs i) ε ∩ A) := by
  rw [withDensity_apply _ hA, aux_kdeds_density hε xs, lintegral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [lintegral_indicator_const (by rw [box]; exact Metric.isClosed_closedBall.measurableSet),
      Measure.restrict_apply (by rw [box]; exact Metric.isClosed_closedBall.measurableSet)]
  · intro i _
    exact measurable_const.indicator (by rw [box]; exact Metric.isClosed_closedBall.measurableSet)

end DistInterpRO.Consistency

open DistInterpRO.Consistency

theorem solution {m n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    (xs : Fin n → Fin m → ℝ) :
    volume.withDensity (fun x => ENNReal.ofReal (kde ε xs x)) ∈
      distSet (fun i => box (xs i) ε) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨⟨?_⟩, ?_⟩
  · rw [aux_kdeds_apply hε xs _ MeasurableSet.univ]
    simp_rw [Set.inter_univ, aux_kdeds_mass hn hε]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_one_div_cancel hn'.ne', ENNReal.ofReal_one]
  · intro S
    have hU : MeasurableSet (⋃ i ∈ S, box (xs i) ε) :=
      Finset.measurableSet_biUnion S (fun i _ => by
        rw [box]; exact Metric.isClosed_closedBall.measurableSet)
    rw [aux_kdeds_apply hε xs _ hU]
    calc ENNReal.ofReal ((S.card : ℝ) / n)
        = ∑ i ∈ S, ENNReal.ofReal (1 / (n : ℝ)) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), Finset.sum_const,
            nsmul_eq_mul, mul_one_div]
      _ = ∑ i ∈ S, ENNReal.ofReal (((n : ℝ) * ε ^ m)⁻¹ * (1 / (2 : ℝ) ^ m))
            * volume (box (xs i) ε ∩ ⋃ j ∈ S, box (xs j) ε) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          have hsub : box (xs i) ε ⊆ ⋃ j ∈ S, box (xs j) ε :=
            Set.subset_iUnion₂ (s := fun j (_ : j ∈ S) => box (xs j) ε) i hi
          rw [Set.inter_eq_left.mpr hsub, aux_kdeds_mass hn hε]
      _ ≤ ∑ i : Fin n, ENNReal.ofReal (((n : ℝ) * ε ^ m)⁻¹ * (1 / (2 : ℝ) ^ m))
            * volume (box (xs i) ε ∩ ⋃ j ∈ S, box (xs j) ε) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ S)
