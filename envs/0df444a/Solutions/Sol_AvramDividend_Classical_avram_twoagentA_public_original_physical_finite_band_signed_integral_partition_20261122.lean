-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_original_physical_finite_band_signed_integral_partition_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:13:20.952217+00:00
-- url     : https://prove2.me/submissions/10a99a25-fd13-4578-8f96-d4a064709a4e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_marked_interval_integral_adjacent_additivity_20261122
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0) (n m : ℕ)
    (hnm : n ≤ m)
    (hInt : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2)
      (Ioc (0 : ℝ≥0) T ×ˢ
        Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) μ) :
    (∫ p in Ioc (0 : ℝ≥0) T ×ˢ
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))), p.2 ∂μ) =
    ∑ i ∈ Finset.Ico n m,
      ∫ p in Ioc (0 : ℝ≥0) T ×ˢ
        Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2))), p.2 ∂μ := by
  classical
  induction m, hnm using Nat.le_induction with
  | base =>
      simp
  | succ m hm ih =>
      let a : ℝ := -(1 / ((n : ℝ) + 1))
      let b : ℝ := -(1 / ((m : ℝ) + 1))
      let c : ℝ := -(1 / ((m : ℝ) + 2))
      have hAB : a ≤ b := by
        have hr : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
          exact_mod_cast Nat.add_le_add_right hm 1
        have hi := one_div_le_one_div_of_le
          (show (0 : ℝ) < (n : ℝ) + 1 by positivity) hr
        dsimp [a, b]
        linarith
      have hBC : b ≤ c := by
        have hi := one_div_le_one_div_of_le
          (show (0 : ℝ) < (m : ℝ) + 1 by positivity)
          (show (m : ℝ) + 1 ≤ (m : ℝ) + 2 by linarith)
        dsimp [b, c]
        linarith
      have hIntFull : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2)
          (Ioc (0 : ℝ≥0) T ×ˢ Ioc a c) μ := by
        simpa [a, c, Nat.cast_add, add_assoc, one_add_one_eq_two] using hInt
      have hSub :
          (Ioc (0 : ℝ≥0) T ×ˢ Ioc a b) ⊆
            (Ioc (0 : ℝ≥0) T ×ˢ Ioc a c) := by
        intro p hp
        exact ⟨hp.1, ⟨hp.2.1, le_trans hp.2.2 hBC⟩⟩
      have hOld : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2)
          (Ioc (0 : ℝ≥0) T ×ˢ Ioc a b) μ :=
        hIntFull.mono_set hSub
      have hSplit :=
        avram_twoagentA_public_original_marked_interval_integral_adjacent_additivity_20261122
          μ T a b c hAB hBC hIntFull
      calc
        (∫ p in Ioc (0 : ℝ≥0) T ×ˢ
          Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / (((m + 1 : ℕ) : ℝ) + 1))),
          p.2 ∂μ) =
            (∫ p in Ioc (0 : ℝ≥0) T ×ˢ Ioc a c, p.2 ∂μ) := by
              simp [a, c, Nat.cast_add, add_assoc, one_add_one_eq_two]
        _ = (∫ p in Ioc (0 : ℝ≥0) T ×ˢ Ioc a b, p.2 ∂μ) +
            (∫ p in Ioc (0 : ℝ≥0) T ×ˢ Ioc b c, p.2 ∂μ) := hSplit
        _ = (∑ i ∈ Finset.Ico n m,
              ∫ p in Ioc (0 : ℝ≥0) T ×ˢ
                Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2))),
                p.2 ∂μ) +
            (∫ p in Ioc (0 : ℝ≥0) T ×ˢ Ioc b c, p.2 ∂μ) := by
              simpa only [a, b] using congrArg
                (fun x : ℝ => x + (∫ p in Ioc (0 : ℝ≥0) T ×ˢ Ioc b c, p.2 ∂μ))
                (ih hOld)
        _ = ∑ i ∈ Finset.Ico n (m + 1),
              ∫ p in Ioc (0 : ℝ≥0) T ×ˢ
                Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2))),
                p.2 ∂μ := by
              rw [Nat.Ico_succ_right_eq_insert_Ico hm]
              simp [Finset.sum_insert, a, b, c, add_comm]
