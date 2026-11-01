-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_finite_rank_predictable_marked_grid_l2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:36:38.802316+00:00
-- url     : https://prove2.me/submissions/6096a27f-f69c-4db9-93f4-ec6c65cf1532

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_rank_marked_poisson_cell_l2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_marked_future_cross_orthogonality

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators

/-- Exact L² isometry for an original-space finite predictable time grid with
a separate, finitely ranked past-dependent mark profile in each cell. -/
theorem solution
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (s : Finset ι) (W : ℕ → ι → Ω → ℝ) (f : ℕ → ι → E → ℝ)
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E) (r : ℕ → ℝ≥0)
    (hKm : ∀ i, Measurable (K i)) (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) μ)
    (hYm : ∀ i n, Measurable (Y i n)) (hYL : ∀ i n, HasLaw (Y i n) ν μ)
    (hYi : ∀ i, iIndepFun (Y i) μ) (hCountMarks : ∀ i,
      IndepFun (K i) (fun ω (n : ℕ) => Y i n ω) μ)
    (hWm : ∀ i a, a ∈ s → Measurable (W i a))
    (hW2 : ∀ i a, a ∈ s → Integrable (fun ω => W i a ω ^ 2) μ)
    (hPast : ∀ i a, a ∈ s →
      IndepFun (W i a) (fun ω => (K i ω, fun n : ℕ => Y i n ω)) μ)
    (hPastSum : ∀ i a, a ∈ s → ∀ b, b ∈ s →
      IndepFun (fun ω => W i a ω + W i b ω)
        (fun ω => (K i ω, fun n : ℕ => Y i n ω)) μ)
    (hfm : ∀ i a, a ∈ s → Measurable (f i a))
    (hfI : ∀ i a, a ∈ s → Integrable (f i a) ν) (hf2 : ∀ i a, a ∈ s → MemLp (f i a) 2 ν)
    (hPrefixMeas : ∀ i, Measurable (fun ω =>
      ∑ j ∈ Finset.range i, ∑ a ∈ s,
        W j a ω * ((∑ n ∈ Finset.range (K j ω), f j a (Y j n ω)) -
          (r j : ℝ) * ∫ z, f j a z ∂ν)))
    (hJointPast : ∀ i a, a ∈ s →
      IndepFun (fun ω =>
        ((∑ j ∈ Finset.range i, ∑ b ∈ s,
          W j b ω * ((∑ n ∈ Finset.range (K j ω), f j b (Y j n ω)) -
            (r j : ℝ) * ∫ z, f j b z ∂ν)), W i a ω))
      (fun ω => (K i ω, fun n : ℕ => Y i n ω)) μ)
    (m : ℕ) :
    Integrable (fun ω => (∑ i ∈ Finset.range m, ∑ a ∈ s,
      W i a ω * ((∑ n ∈ Finset.range (K i ω), f i a (Y i n ω)) -
        (r i : ℝ) * ∫ z, f i a z ∂ν)) ^ 2) μ ∧
    (∫ ω, (∑ i ∈ Finset.range m, ∑ a ∈ s,
      W i a ω * ((∑ n ∈ Finset.range (K i ω), f i a (Y i n ω)) -
        (r i : ℝ) * ∫ z, f i a z ∂ν)) ^ 2 ∂μ) =
      ∑ i ∈ Finset.range m, ∑ a ∈ s, ∑ b ∈ s,
        (∫ ω, W i a ω * W i b ω ∂μ) * (r i : ℝ) *
          (∫ z, f i a z * f i b z ∂ν) := by
  classical
  let Z : ℕ → Ω → ℝ := fun i ω => ∑ a ∈ s,
    W i a ω * ((∑ n ∈ Finset.range (K i ω), f i a (Y i n ω)) -
      (r i : ℝ) * ∫ z, f i a z ∂ν)
  let P : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ Finset.range m, Z i ω
  change Integrable (fun ω => P m ω ^ 2) μ ∧
    (∫ ω, P m ω ^ 2 ∂μ) =
      ∑ i ∈ Finset.range m, ∑ a ∈ s, ∑ b ∈ s,
        (∫ ω, W i a ω * W i b ω ∂μ) * (r i : ℝ) *
          (∫ z, f i a z * f i b z ∂ν)
  induction m with
  | zero =>
      constructor
      · simpa [P] using
          (integrable_const (0 : ℝ) : Integrable (fun _ : Ω => (0 : ℝ)) μ)
      · simp [P]
  | succ m ih =>
      have hPm : Measurable (P m) := by simpa [P, Z] using hPrefixMeas m
      have hPlp : MemLp (P m) 2 μ :=
        (memLp_two_iff_integrable_sq hPm.aestronglyMeasurable).2 ih.1
      have hCell : Integrable (fun ω => Z m ω ^ 2) μ ∧
          (∫ ω, Z m ω ^ 2 ∂μ) =
            ∑ a ∈ s, ∑ b ∈ s,
              (∫ ω, W m a ω * W m b ω ∂μ) * (r m : ℝ) *
                (∫ z, f m a z * f m b z ∂ν) := by
        simpa [Z] using
          (avram_wave4_p1_finite_rank_marked_poisson_cell_l2_isometry
            μ ν s (W m) (f m) (K m) (Y m)
            (hKm m) (r m) (hKlaw m)
            (hYm m) (hYL m) (hYi m) (hCountMarks m)
            (hWm m) (hW2 m) (hPast m) (hPastSum m)
            (hfm m) (hfI m) (hf2 m))
      have hCrossOne (a : ι) (ha : a ∈ s) :
          Integrable (fun ω => P m ω * (W m a ω *
            ((∑ n ∈ Finset.range (K m ω), f m a (Y m n ω)) -
              (r m : ℝ) * ∫ z, f m a z ∂ν))) μ ∧
          (∫ ω, P m ω * (W m a ω *
            ((∑ n ∈ Finset.range (K m ω), f m a (Y m n ω)) -
              (r m : ℝ) * ∫ z, f m a z ∂ν)) ∂μ) = 0 := by
        have hWlp : MemLp (W m a) 2 μ :=
          (memLp_two_iff_integrable_sq
            (hWm m a ha).aestronglyMeasurable).2 (hW2 m a ha)
        simpa only [mul_assoc] using
          (avram_wave4_p1_marked_future_cross_orthogonality
            μ ν (P m) (W m a) hPm (hWm m a ha)
            hPlp hWlp (K m) (Y m) (hKm m) (r m) (hKlaw m)
            (hYm m) (hYL m) (hCountMarks m)
            (hJointPast m a ha) (f m a) (hfm m a ha) (hfI m a ha))
      have hCrossFun :
          (fun ω => P m ω * Z m ω) =
          (fun ω => ∑ a ∈ s, P m ω * (W m a ω *
            ((∑ n ∈ Finset.range (K m ω), f m a (Y m n ω)) -
              (r m : ℝ) * ∫ z, f m a z ∂ν))) := by
        funext ω; simp only [Z, Finset.mul_sum]
      have hCrossInt : Integrable (fun ω => P m ω * Z m ω) μ := by
        rw [hCrossFun]
        exact integrable_finset_sum s (fun a ha => (hCrossOne a ha).1)
      have hCrossZero : (∫ ω, P m ω * Z m ω ∂μ) = 0 := by
        rw [hCrossFun, integral_finset_sum s
          (fun a ha => (hCrossOne a ha).1)]
        exact Finset.sum_eq_zero (fun a ha => (hCrossOne a ha).2)
      have hPlusSq :
          (fun ω => (P m ω + Z m ω) ^ 2) =
          (fun ω => P m ω ^ 2 + Z m ω ^ 2 +
            2 * (P m ω * Z m ω)) := by
        funext ω; ring
      have hPlusInt : Integrable (fun ω => (P m ω + Z m ω) ^ 2) μ := by
        rw [hPlusSq]
        exact (ih.1.add hCell.1).add (hCrossInt.const_mul 2)
      have hAddSq : (∫ ω, P m ω ^ 2 + Z m ω ^ 2 ∂μ) =
          (∫ ω, P m ω ^ 2 ∂μ) +
            (∫ ω, Z m ω ^ 2 ∂μ) := by
        simpa only [Pi.add_apply] using integral_add ih.1 hCell.1
      have hAddCross : (∫ ω,
          P m ω ^ 2 + Z m ω ^ 2 + 2 * (P m ω * Z m ω) ∂μ) =
          (∫ ω, P m ω ^ 2 + Z m ω ^ 2 ∂μ) +
            (∫ ω, 2 * (P m ω * Z m ω) ∂μ) := by
        simpa only [Pi.add_apply] using
          integral_add (ih.1.add hCell.1) (hCrossInt.const_mul 2)
      have hNext :
          (fun ω => P (m + 1) ω ^ 2) =
          (fun ω => (P m ω + Z m ω) ^ 2) := by
        funext ω
        simp only [P, Finset.sum_range_succ]
      constructor
      · rw [hNext]
        exact hPlusInt
      · calc
          (∫ ω, P (m + 1) ω ^ 2 ∂μ) =
              (∫ ω, (P m ω + Z m ω) ^ 2 ∂μ) := by rw [hNext]
          _ = (∫ ω, P m ω ^ 2 ∂μ) +
              (∫ ω, Z m ω ^ 2 ∂μ) := by
            rw [hPlusSq, hAddCross, hAddSq, integral_const_mul, hCrossZero]
            ring
          _ = ∑ i ∈ Finset.range (m + 1), ∑ a ∈ s, ∑ b ∈ s,
                (∫ ω, W i a ω * W i b ω ∂μ) * (r i : ℝ) *
                  (∫ z, f i a z * f i b z ∂ν) := by
            rw [Finset.sum_range_succ, ih.2, hCell.2]
