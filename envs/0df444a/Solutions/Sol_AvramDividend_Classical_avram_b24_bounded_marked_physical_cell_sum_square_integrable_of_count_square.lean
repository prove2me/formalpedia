-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_bounded_marked_physical_cell_sum_square_integrable_of_count_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:06:52.773212+00:00
-- url     : https://prove2.me/submissions/54083ebb-4175-4ff8-974b-3f772923ffb8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (marked : Ω → Finset ℕ)
    (hCount2 : Integrable (fun ω => ((marked ω).card : ℝ)^2) P)
    (W : ℕ → Ω → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hW : ∀ i ω, |W i ω| ≤ L)
    (hMeas : AEStronglyMeasurable
      (fun ω => (∑ i ∈ marked ω, W i ω)^2) P) :
    Integrable (fun ω => (∑ i ∈ marked ω, W i ω)^2) P := by
  have hBound (ω : Ω) :
      |∑ i ∈ marked ω, W i ω| ≤ ((marked ω).card : ℝ) * L := by
    calc
      _ ≤ ∑ i ∈ marked ω, |W i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ marked ω, L := Finset.sum_le_sum (by
        intro i hi
        exact hW i ω)
      _ = ((marked ω).card : ℝ) * L := by simp
  have hLsq : 0 ≤ L ^ 2 := sq_nonneg _
  have hCnonneg (ω : Ω) : 0 ≤ ((marked ω).card : ℝ) * L :=
    mul_nonneg (Nat.cast_nonneg _) hL
  refine Integrable.mono' (hCount2.const_mul (L ^ 2)) hMeas ?_
  filter_upwards [] with ω
  have hb := hBound ω
  have hz : 0 ≤ (∑ i ∈ marked ω, W i ω) ^ 2 := sq_nonneg _
  have hs : (∑ i ∈ marked ω, W i ω) ^ 2 ≤
      L ^ 2 * ((marked ω).card : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb)
      (add_nonneg (hCnonneg ω) (abs_nonneg (∑ i ∈ marked ω, W i ω))),
      sq_abs (∑ i ∈ marked ω, W i ω)]
  simpa [Real.norm_eq_abs, abs_of_nonneg hz,
    abs_of_nonneg (mul_nonneg hLsq (sq_nonneg _)), mul_comm] using hs
