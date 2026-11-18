-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB52_original_barrier_masked_physical_noise_sum_eq_first_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:37:35.575559+00:00
-- url     : https://prove2.me/submissions/c21f2106-40d4-4976-bfcb-b388dbcc5587

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_barrier_postpayment_rightLimit_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Every masked original Gaussian physical-grid noise sum is linear on the tube. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (ω : Ω)
    (hTube : ∀ u : ℝ≥0, u ≤ T →
      |X.X u ω| ≤ (1 / 400 : ℝ))
    (m : ℕ) (s : ℕ → ℝ≥0) (Z : ℕ → ℝ)
    (q a v : ℝ) (w : ℝ → ℝ) :
    let Y : ℕ → ℝ := fun i =>
      (1 / 8 : ℝ) + X.X (s i) ω -
        rightLimit (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (s i) ω
    (Finset.range (m + 1)).sum (fun i =>
      (if s i < T then Real.exp (-(q * (s i : ℝ))) *
        (if Y i ∈ Icc a (5 / 44 : ℝ) then deriv w (Y i) else 1)
       else 0) * Z i +
      (if s i < T then (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) *
        (if Y i ∈ Icc a (5 / 44 : ℝ)
         then iteratedDeriv 2 w (Y i) else 0)
       else 0) * (Z i ^ 2 - v)) =
    (Finset.range (m + 1)).sum (fun i =>
      if s i < T then Real.exp (-(q * (s i : ℝ))) * Z i else 0)
    := by
  dsimp
  apply Finset.sum_congr rfl
  intro i _
  by_cases hs : s i < T
  · have hR :=
      avram_gbB41_original_barrier_postpayment_rightLimit_eq
        X (1 / 8 : ℝ) ω (s i)
    have hB :=
      avram_gbB38_barrier_reserve_above_cutoff_on_tube
        X (s i) ω (fun u hu => hTube u (hu.trans (le_of_lt hs)))
    have hY : (5 / 44 : ℝ) <
        (1 / 8 : ℝ) + X.X (s i) ω -
          rightLimit (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (s i) ω := by
      change (5 / 44 : ℝ) < (1 / 8 : ℝ) + X.X (s i) ω -
        barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) (s i) ω at hB
      rw [hR]
      exact hB
    have hNot : (1 / 8 : ℝ) + X.X (s i) ω -
        rightLimit (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (s i) ω ∉
          Icc a (5 / 44 : ℝ) := by
      intro hMem
      exact (not_le_of_gt hY) hMem.2
    simp only [if_pos hs, if_neg hNot, mul_one, mul_zero, zero_mul, add_zero]
  · simp [hs]
