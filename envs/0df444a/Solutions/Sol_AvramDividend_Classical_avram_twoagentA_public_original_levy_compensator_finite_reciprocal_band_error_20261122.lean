-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_original_levy_compensator_finite_reciprocal_band_error_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:13:27.878609+00:00
-- url     : https://prove2.me/submissions/807c6a1e-e397-4ab4-839e-fba414ebaa81

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_levy_signed_mark_band_generic_integrand_finite_annulus_chain_20261122
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_levy_single_reciprocal_signed_mark_vs_mass_error_20261122
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (n m : ℕ) (hnm : n ≤ m)
    (hMono : Monotone (fun i : ℕ => -(1 / ((i : ℝ) + 1))))
    (hFin : ∀ i ∈ Finset.Ico n m,
      ν (Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))) < ⊤)
    (hLin : IntegrableOn (fun z : ℝ => z)
      (Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) ν) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let A : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let c : ℕ → ℝ := fun i => -(1 / ((i : ℝ) + 1))
    let δ : ℕ → ℝ := fun i =>
      1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
    |(∫ z in B, z ∂ν) -
      ∑ i ∈ Finset.Ico n m, c i * (ν (A i)).toReal| ≤
      ∑ i ∈ Finset.Ico n m, δ i * (ν (A i)).toReal := by
  classical
  let a : ℕ → ℝ := fun i => -(1 / ((i : ℝ) + 1))
  let B : Set ℝ := Ioc (a n) (a m)
  let A : ℕ → Set ℝ := fun i =>
    Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
  let c : ℕ → ℝ := fun i => -(1 / ((i : ℝ) + 1))
  let δ : ℕ → ℝ := fun i =>
    1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
  change |(∫ z in B, z ∂ν) -
    ∑ i ∈ Finset.Ico n m, c i * (ν (A i)).toReal| ≤
    ∑ i ∈ Finset.Ico n m, δ i * (ν (A i)).toReal
  have hChain :
      (∫ z in B, z ∂ν) =
        ∑ i ∈ Finset.Ico n m, (∫ z in A i, z ∂ν) := by
    simpa [a, A, B, Nat.cast_succ, add_assoc, one_add_one_eq_two] using
      avram_twoagentA_public_original_levy_signed_mark_band_generic_integrand_finite_annulus_chain_20261122
        ν a hMono (fun z : ℝ => z) n m hnm hLin
  have hPiece : ∀ i ∈ Finset.Ico n m,
      |(∫ z in A i, z ∂ν) - c i * (ν (A i)).toReal| ≤
        δ i * (ν (A i)).toReal := by
    intro i hi
    have him := Finset.mem_Ico.mp hi
    have hSubset : A i ⊆ B := by
      intro z hz
      have hzA : z ∈ Ioc (a i) (a (i + 1)) := by
        simpa [A, a, Nat.cast_succ, add_assoc, one_add_one_eq_two] using hz
      change z ∈ Ioc (a n) (a m)
      exact ⟨lt_of_le_of_lt (hMono him.1) hzA.1,
        le_trans hzA.2 (hMono (Nat.succ_le_of_lt him.2))⟩
    have hLinI : IntegrableOn (fun z : ℝ => z) (A i) ν :=
      hLin.mono_set hSubset
    have hOne :=
      avram_twoagentA_public_original_levy_single_reciprocal_signed_mark_vs_mass_error_20261122
        ν i (hFin i hi) hLinI
    simpa [A, c, δ] using hOne
  calc
    |(∫ z in B, z ∂ν) -
      ∑ i ∈ Finset.Ico n m, c i * (ν (A i)).toReal| =
      |∑ i ∈ Finset.Ico n m,
        ((∫ z in A i, z ∂ν) - c i * (ν (A i)).toReal)| := by
          rw [hChain, Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ Finset.Ico n m,
      |(∫ z in A i, z ∂ν) - c i * (ν (A i)).toReal| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.Ico n m, δ i * (ν (A i)).toReal :=
      Finset.sum_le_sum hPiece
