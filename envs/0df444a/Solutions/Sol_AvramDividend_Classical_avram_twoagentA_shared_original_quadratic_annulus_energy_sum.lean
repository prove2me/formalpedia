-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_shared_original_quadratic_annulus_energy_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:46:34.208318+00:00
-- url     : https://prove2.me/submissions/266d144b-7bda-4c10-920b-79e9b0d90b3d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_negative_mark_integrated_quadratic_energy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_levy_quadratic_annulus_integral_chain
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (n m : ℕ) (hnm : n ≤ m)
    (hMono : Monotone (fun i : ℕ => -(1 / ((i : ℝ) + 1))))
    (hFin : ∀ i ∈ Finset.Ico n m,
      ν (Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))) < ⊤)
    (hSq : IntegrableOn (fun z : ℝ => z ^ 2)
      (Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) ν) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let A : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let c : ℕ → ℝ := fun i => -(1 / ((i : ℝ) + 1))
    let δ : ℕ → ℝ := fun i =>
      1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
    (∑ i ∈ Finset.Ico n m, δ i * (ν (A i)).toReal) ≤
      2 * (∫ z in B, z ^ 2 ∂ν) ∧
    (∑ i ∈ Finset.Ico n m, c i ^ 2 * (ν (A i)).toReal) ≤
      4 * (∫ z in B, z ^ 2 ∂ν) := by
  classical
  let a : ℕ → ℝ := fun i => -(1 / ((i : ℝ) + 1))
  let B : Set ℝ := Ioc (a n) (a m)
  let A : ℕ → Set ℝ := fun i =>
    Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
  let c : ℕ → ℝ := fun i => -(1 / ((i : ℝ) + 1))
  let δ : ℕ → ℝ := fun i =>
    1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
  change (∑ i ∈ Finset.Ico n m, δ i * (ν (A i)).toReal) ≤
      2 * (∫ z in B, z ^ 2 ∂ν) ∧
    (∑ i ∈ Finset.Ico n m, c i ^ 2 * (ν (A i)).toReal) ≤
      4 * (∫ z in B, z ^ 2 ∂ν)
  have hChain :
      (∫ z in B, z ^ 2 ∂ν) =
        ∑ i ∈ Finset.Ico n m, (∫ z in A i, z ^ 2 ∂ν) := by
    simpa [a, A, B, Nat.cast_succ, add_assoc, one_add_one_eq_two] using
      avram_twoagentA_shared_levy_quadratic_annulus_integral_chain
        ν a hMono n m hnm hSq
  have hPiece : ∀ i ∈ Finset.Ico n m,
      δ i * (ν (A i)).toReal ≤ 2 * (∫ z in A i, z ^ 2 ∂ν) ∧
      c i ^ 2 * (ν (A i)).toReal ≤ 4 * (∫ z in A i, z ^ 2 ∂ν) := by
    intro i hi
    have him := Finset.mem_Ico.mp hi
    have hSubset : A i ⊆ B := by
      intro z hz
      have hzA : z ∈ Ioc (a i) (a (i + 1)) := by
        simpa [A, a, Nat.cast_succ, add_assoc, one_add_one_eq_two] using hz
      change z ∈ Ioc (a n) (a m)
      exact ⟨lt_of_le_of_lt (hMono him.1) hzA.1,
        le_trans hzA.2 (hMono (Nat.succ_le_of_lt him.2))⟩
    have hSqI : IntegrableOn (fun z : ℝ => z ^ 2) (A i) ν :=
      hSq.mono_set hSubset
    have hOne :=
      avram_twoagentA_shared_negative_mark_integrated_quadratic_energy
        ν i (hFin i hi) hSqI
    simpa [A, c, δ] using hOne
  constructor
  · have h := Finset.sum_le_sum (fun i hi => (hPiece i hi).1)
    simpa [Finset.mul_sum, hChain] using h
  · have h := Finset.sum_le_sum (fun i hi => (hPiece i hi).2)
    simpa [Finset.mul_sum, hChain] using h
