-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict12_original_single_contact_raw_residual_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:06:40.127258+00:00
-- url     : https://prove2.me/submissions/393a1bdc-8449-4127-9bf9-75a078cfdad8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict12_original_masked_stop_grid_residual_contact_identity
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict12_original_contact_correction_crossing_support
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict12_original_unique_ruin_contact_cell
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Every original strict pre-ruin masked grid residual equals a clipped
    residual plus either zero or the correction at one ruin-crossing cell. -/
theorem solution
    (n : ℕ) (u : ℕ → ℝ≥0) (τ : ℝ≥0) (R : ℝ≥0 → ℝ)
    (W : ℕ → ℝ) (E : ℕ → Prop) (hmono : Monotone u)
    (hE : ∀ i, E i → u i < τ) :
    let Raw := ∑ i ∈ Finset.range n,
      if E i then W i * (R (u i) - R (u (i + 1))) else 0
    let Stopped := ∑ i ∈ Finset.range n,
      if E i then
        W i * (R (min (u i) τ) - R (min (u (i + 1)) τ)) else 0
    ∃ t : ℝ, Raw = Stopped + t ∧
      (t = 0 ∨ ∃ i ∈ Finset.range n,
        E i ∧ τ < u (i + 1) ∧
          t = W i * (R τ - R (u (i + 1)))) := by
  classical
  let g : ℕ → ℝ := fun i =>
    if E i ∧ τ < u (i + 1) then W i * (R τ - R (u (i + 1))) else 0
  refine ⟨∑ i ∈ Finset.range n, g i, ?_, ?_⟩
  · calc
      _ = _ + (∑ i ∈ Finset.range n,
          if E i then
            W i * (R (min (u (i + 1)) τ) - R (u (i + 1))) else 0) :=
        avram_bv_strict12_original_masked_stop_grid_residual_contact_identity
          n u τ R W E hE
      _ = _ + (∑ i ∈ Finset.range n, g i) := by
        rw [avram_bv_strict12_original_contact_correction_crossing_support
          n u τ R W E]
  · by_cases hex : ∃ i ∈ Finset.range n, E i ∧ τ < u (i + 1)
    · right
      obtain ⟨i, hi, hiE, hiCross⟩ := hex
      refine ⟨i, hi, hiE, hiCross, ?_⟩
      have hsingle : (∑ j ∈ Finset.range n, g j) = g i := by
        apply Finset.sum_eq_single i
        · intro j hj hji
          by_cases hjE : E j ∧ τ < u (j + 1)
          · have hCrossI : u i < τ ∧ τ ≤ u (i + 1) :=
              ⟨hE i hiE, le_of_lt hiCross⟩
            have hCrossJ : u j < τ ∧ τ ≤ u (j + 1) :=
              ⟨hE j hjE.1, le_of_lt hjE.2⟩
            have hEq := avram_bv_strict12_original_unique_ruin_contact_cell
              u τ hmono i j hCrossI hCrossJ
            exact False.elim (hji hEq.symm)
          · simp [g, hjE]
        · intro hnot
          exact False.elim (hnot hi)
      simpa [g, hiE, hiCross] using hsingle
    · left
      apply Finset.sum_eq_zero
      intro i hi
      have hnot : ¬ (E i ∧ τ < u (i + 1)) := by
        intro hiE
        exact hex ⟨i, hi, hiE⟩
      simp [g, hnot]
