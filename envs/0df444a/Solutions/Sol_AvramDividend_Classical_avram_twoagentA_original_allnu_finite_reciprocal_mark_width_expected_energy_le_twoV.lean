-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_original_allnu_finite_reciprocal_mark_width_expected_energy_le_twoV
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:54:28.919393+00:00
-- url     : https://prove2.me/submissions/b40d9538-f2c9-4a34-be68-a3dec4563035

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_negative_reciprocal_endpoint_monotone
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_finite_negative_band_facts
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_quadratic_annulus_energy_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_quadratic_real_energy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let A : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let r : ℕ → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (A i)).toReal
    let δ : ℕ → ℝ := fun i =>
      1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
    let V : ℝ := (T : ℝ) * (∫ z in B, z ^ 2 ∂X.ν)
    (∑ i ∈ Finset.Ico n m, δ i * r i) ≤ 2 * V := by
  classical
  let B : Set ℝ :=
    Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let A : ℕ → Set ℝ := fun i =>
    Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
  let r : ℕ → ℝ := fun i =>
    ((T : ℝ≥0∞) * X.ν (A i)).toReal
  let δ : ℕ → ℝ := fun i =>
    1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
  let V : ℝ := (T : ℝ) * (∫ z in B, z ^ 2 ∂X.ν)
  change (∑ i ∈ Finset.Ico n m, δ i * r i) ≤ 2 * V
  have hFin : ∀ i ∈ Finset.Ico n m, X.ν (A i) < ⊤ := by
    intro i hi
    have h :=
      (avram_twoagentA_shared_original_finite_negative_band_facts
        X i (i + 1)).2.2
    simpa [A, Nat.cast_succ, add_assoc, one_add_one_eq_two] using h
  have hMono :=
    avram_twoagentA_shared_negative_reciprocal_endpoint_monotone
  have hSq : IntegrableOn (fun z : ℝ => z ^ 2) B X.ν := by
    have hSource := (avram_p4_h_gaussian_original_nu_quadratic_real_energy X n).1
    apply hSource.mono_set
    intro z hz
    have hPositive : 0 < 1 / ((m : ℝ) + 1) := by positivity
    exact ⟨hz.1,
      le_of_lt (lt_of_le_of_lt hz.2 (neg_neg_of_pos hPositive))⟩
  have hδBudget : (∑ i ∈ Finset.Ico n m,
      δ i * (X.ν (A i)).toReal) ≤
      2 * (∫ z in B, z ^ 2 ∂X.ν) := by
    have h :=
      (avram_twoagentA_shared_original_quadratic_annulus_energy_sum
        X.ν n m hnm hMono hFin hSq).1
    simpa [A, B, δ] using h
  have hr (i : ℕ) :
      r i = (T : ℝ) * (X.ν (A i)).toReal := by
    simp [r, ENNReal.toReal_mul, ENNReal.coe_toReal]
  calc
    (∑ i ∈ Finset.Ico n m, δ i * r i) =
        (T : ℝ) * (∑ i ∈ Finset.Ico n m,
          δ i * (X.ν (A i)).toReal) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hr]
      ring
    _ ≤ (T : ℝ) * (2 * (∫ z in B, z ^ 2 ∂X.ν)) :=
      mul_le_mul_of_nonneg_left hδBudget (by positivity)
    _ = 2 * V := by dsimp [V]; ring
