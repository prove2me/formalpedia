-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_original_intrinsic_measure_and_downward_residual_partition_source_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:05:21.606618+00:00
-- url     : https://prove2.me/submissions/34b48ae1-1e5d-4475-b8ab-e350fc07fd3b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_intrinsic_negative_mark_measure_finite_real_interval_additivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The entire actual BV source drift-minus-path increment is exactly
the finite accumulated intrinsic source negative marks plus the finite
downward residual variation on every increasing time partition. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ (R : ℝ≥0 → ℝ) (J : ℝ≥0 → ℝ≥0 → ℝ),
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      (∀ (a b : ℝ≥0),
        J a b =
          (∫⁻ p,
            (if a < p.1 ∧ p.1 ≤ b then ENNReal.ofReal (-p.2) else 0) ∂
            ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))).toReal) ∧
      Monotone R ∧
      ∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ),
        (∑ i ∈ Finset.range n,
          (J (u i) (u (i + 1)) +
            (R (u (i + 1)) - R (u i)))) =
          ((u n : ℝ) - (u 0 : ℝ)) * X.drift -
            (X.X (u n) ω - X.X (u 0) ω) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition
      X hBV,
      avram_wave5_04a_actual_bv_intrinsic_negative_mark_measure_finite_real_interval_additivity
      X hBV] with ω hsource hmeasure
  obtain ⟨R, hRdef, hRmono, hinterval⟩ := hsource
  obtain ⟨J, hJdef, hJnonneg, hJadd⟩ := hmeasure
  refine ⟨R, J, hRdef, hJdef, hRmono, ?_⟩
  intro u hu n
  have hJzero (t : ℝ≥0) : J t t = 0 := by
    have h := hJadd t t t le_rfl le_rfl
    linarith only [h]
  have hJsum (k : ℕ) :
      (∑ i ∈ Finset.range k, J (u i) (u (i + 1))) =
        J (u 0) (u k) := by
    induction k with
    | zero => simp [hJzero]
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        exact (hJadd (u 0) (u k) (u (k + 1))
          (hu (Nat.zero_le k)) (hu (Nat.le_succ k))).symm
  have hRsum (k : ℕ) :
      (∑ i ∈ Finset.range k,
        (R (u (i + 1)) - R (u i))) =
        R (u k) - R (u 0) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hsourceEnd := hinterval (u 0) (u n) (hu (Nat.zero_le n))
  rw [← hJdef (u 0) (u n)] at hsourceEnd
  calc
    (∑ i ∈ Finset.range n,
      (J (u i) (u (i + 1)) +
        (R (u (i + 1)) - R (u i)))) =
      (∑ i ∈ Finset.range n, J (u i) (u (i + 1))) +
        (∑ i ∈ Finset.range n,
          (R (u (i + 1)) - R (u i))) := by
          rw [Finset.sum_add_distrib]
    _ = J (u 0) (u n) + (R (u n) - R (u 0)) := by
          rw [hJsum n, hRsum n]
    _ = ((u n : ℝ) - (u 0 : ℝ)) * X.drift -
          (X.X (u n) ω - X.X (u 0) ω) := by
          linarith only [hsourceEnd]
