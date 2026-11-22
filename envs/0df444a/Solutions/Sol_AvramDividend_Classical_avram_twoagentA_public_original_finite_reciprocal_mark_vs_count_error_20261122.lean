-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_original_finite_reciprocal_mark_vs_count_error_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:17:02.930673+00:00
-- url     : https://prove2.me/submissions/d781d0ad-6b6a-4c85-969d-6a6cc3c78399

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_physical_finite_band_signed_integral_partition_20261122
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_physical_signed_mark_constant_shift_integral_20261122
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_time_mark_negative_bin_integral_error_20261122
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
set_option autoImplicit false

theorem solution
    (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m)
    (hMono : Monotone (fun i : ℕ => -(1 / ((i : ℝ) + 1))))
    (hFinite : μ (Ioc 0 T ×ˢ
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) < ⊤)
    (hInt : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2)
      (Ioc 0 T ×ˢ
        Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) μ) :
    let B : Set (ℝ≥0 × ℝ) := Ioc 0 T ×ˢ
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let A : ℕ → Set (ℝ≥0 × ℝ) := fun i => Ioc 0 T ×ˢ
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let c : ℕ → ℝ := fun i => -(1 / ((i : ℝ) + 1))
    let δ : ℕ → ℝ := fun i =>
      1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
    |(∫ p in B, p.2 ∂μ) -
      ∑ i ∈ Finset.Ico n m, c i * (μ (A i)).toReal| ≤
      ∑ i ∈ Finset.Ico n m, δ i * (μ (A i)).toReal := by
  classical
  let B : Set (ℝ≥0 × ℝ) := Ioc 0 T ×ˢ
    Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let A : ℕ → Set (ℝ≥0 × ℝ) := fun i => Ioc 0 T ×ˢ
    Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
  let c : ℕ → ℝ := fun i => -(1 / ((i : ℝ) + 1))
  let δ : ℕ → ℝ := fun i =>
    1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
  change |(∫ p in B, p.2 ∂μ) -
      ∑ i ∈ Finset.Ico n m, c i * (μ (A i)).toReal| ≤
      ∑ i ∈ Finset.Ico n m, δ i * (μ (A i)).toReal
  have hPart :=
    avram_twoagentA_public_original_physical_finite_band_signed_integral_partition_20261122
      μ T n m hnm hInt
  have hCell : ∀ i ∈ Finset.Ico n m,
      |(∫ p in A i, p.2 ∂μ) - c i * (μ (A i)).toReal| ≤
        δ i * (μ (A i)).toReal := by
    intro i hi
    obtain ⟨hni, him⟩ := Finset.mem_Ico.mp hi
    have hSub : A i ⊆ B := by
      intro p hp
      have hU : -(1 / ((i : ℝ) + 2)) ≤
          -(1 / ((m : ℝ) + 1)) := by
        simpa [Nat.cast_add, add_assoc, one_add_one_eq_two] using
          (hMono (Nat.succ_le_of_lt him))
      exact ⟨hp.1, ⟨lt_of_le_of_lt (hMono hni) hp.2.1,
        le_trans hp.2.2 hU⟩⟩
    have hFi : μ (A i) < ⊤ :=
      lt_of_le_of_lt (measure_mono hSub) hFinite
    have hIi : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2) (A i) μ :=
      hInt.mono_set hSub
    have hShift :=
      avram_twoagentA_public_original_physical_signed_mark_constant_shift_integral_20261122
        μ (A i) (1 / ((i : ℝ) + 1)) hFi hIi
    have hErr :=
      avram_twoagentA_public_original_time_mark_negative_bin_integral_error_20261122
        μ T i hFi
    have hWidth : δ i =
        1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)) := by
      dsimp [δ]
      field_simp
      ring
    have hEq :
        (∫ p in A i, p.2 ∂μ) - c i * (μ (A i)).toReal =
          (∫ p in A i, p.2 + 1 / ((i : ℝ) + 1) ∂μ) := by
      dsimp [c]
      rw [hShift]
      ring
    rw [hEq, hWidth]
    simpa [A, Measure.real] using hErr
  calc
    |(∫ p in B, p.2 ∂μ) -
      ∑ i ∈ Finset.Ico n m, c i * (μ (A i)).toReal| =
        |∑ i ∈ Finset.Ico n m,
          ((∫ p in A i, p.2 ∂μ) - c i * (μ (A i)).toReal)| := by
            rw [hPart, Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ Finset.Ico n m,
          |(∫ p in A i, p.2 ∂μ) - c i * (μ (A i)).toReal| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.Ico n m, δ i * (μ (A i)).toReal :=
      Finset.sum_le_sum hCell
