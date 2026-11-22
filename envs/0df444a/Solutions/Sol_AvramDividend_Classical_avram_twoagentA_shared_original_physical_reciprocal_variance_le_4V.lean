-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_shared_original_physical_reciprocal_variance_le_4V
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:53:46.816956+00:00
-- url     : https://prove2.me/submissions/4fbb4134-565f-4ce4-9d08-a223649395be

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_reciprocal_finitebin_isometry
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_quadratic_annulus_energy_sum
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_negative_reciprocal_endpoint_monotone
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_finite_negative_band_facts
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_quadratic_real_energy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let A : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let r : ℕ → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (A i)).toReal
    let S : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.Ico n m,
        (-(1 / ((i : ℝ) + 1))) *
          ((NX ω (Ioc 0 T ×ˢ A i)).toReal - r i)
    let V : ℝ := (T : ℝ) * (∫ z in B, z ^ 2 ∂X.ν)
    (∫ ω, (S ω) ^ 2 ∂P) ≤ 4 * V := by
  classical
  let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let A : ℕ → Set ℝ := fun i => Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {s : ℝ≥0 |
      0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
      (fun s : ℝ≥0 => (s, X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
  let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (A i)).toReal
  let S : Ω → ℝ := fun ω => ∑ i ∈ Finset.Ico n m,
      (-(1 / ((i : ℝ) + 1))) *
        ((NX ω (Ioc 0 T ×ˢ A i)).toReal - r i)
  let V : ℝ := (T : ℝ) * (∫ z in B, z ^ 2 ∂X.ν)
  change (∫ ω, (S ω) ^ 2 ∂P) ≤ 4 * V
  have hMono := avram_twoagentA_shared_negative_reciprocal_endpoint_monotone
  have hFinite : ∀ i ∈ Finset.Ico n m, X.ν (A i) < ⊤ := by
    intro i hi
    have h :=
      (avram_twoagentA_shared_original_finite_negative_band_facts
        X i (i + 1)).2.2
    simpa [A, Nat.cast_succ, add_assoc, one_add_one_eq_two] using h
  have hSq : IntegrableOn (fun z : ℝ => z ^ 2) B X.ν := by
    have hSource :=
      (avram_p4_h_gaussian_original_nu_quadratic_real_energy X n).1
    apply hSource.mono_set
    intro z hz
    have hPositive : 0 < 1 / ((m : ℝ) + 1) := by positivity
    exact ⟨hz.1, le_of_lt (lt_of_le_of_lt hz.2 (neg_neg_of_pos hPositive))⟩
  have hEnergy : (∑ i ∈ Finset.Ico n m,
      (-(1 / ((i : ℝ) + 1))) ^ 2 * (X.ν (A i)).toReal) ≤
      4 * (∫ z in B, z ^ 2 ∂X.ν) := by
    have h :=
      (avram_twoagentA_shared_original_quadratic_annulus_energy_sum
        X.ν n m hnm hMono hFinite hSq).2
    simpa [A, B] using h
  have hIso : (∫ ω, (S ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.Ico n m,
        (-(1 / ((i : ℝ) + 1))) ^ 2 * r i := by
    simpa [S, A, NX, r] using
      (avram_twoagentA_shared_original_reciprocal_finitebin_isometry
        X T n m)
  have hMul (i : ℕ) : r i = (T : ℝ) * (X.ν (A i)).toReal := by
    simp [r, ENNReal.toReal_mul, ENNReal.coe_toReal]
  calc
    (∫ ω, (S ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.Ico n m,
        (-(1 / ((i : ℝ) + 1))) ^ 2 * r i := hIso
    _ = (T : ℝ) * (∑ i ∈ Finset.Ico n m,
        (-(1 / ((i : ℝ) + 1))) ^ 2 * (X.ν (A i)).toReal) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hMul]
      ring
    _ ≤ (T : ℝ) * (4 * (∫ z in B, z ^ 2 ∂X.ν)) :=
      mul_le_mul_of_nonneg_left hEnergy (by positivity)
    _ = 4 * V := by dsimp [V]; ring
