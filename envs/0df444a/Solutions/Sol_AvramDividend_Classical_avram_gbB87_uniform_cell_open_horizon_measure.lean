-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB87_uniform_cell_open_horizon_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:12:38.153145+00:00
-- url     : https://prove2.me/submissions/771dbe55-d2bd-4bc5-a92b-022cb41df074

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    (n N r : ℕ) (hn : 0 < n) (hN : 0 < N) (hr : r < N) :
    let δ : ℝ := (n : ℝ) / (N : ℝ)
    (volume (Ioo (0 : ℝ) (n : ℝ) ∩
      Ico ((r : ℝ) * δ) (((r + 1 : ℕ) : ℝ) * δ))).toReal = δ := by
  intro δ
  let lo : ℝ := (r : ℝ) * δ
  let hi : ℝ := ((r + 1 : ℕ) : ℝ) * δ
  have hδ : 0 < δ := div_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hN)
  have h0 : 0 ≤ lo := mul_nonneg (Nat.cast_nonneg _) (le_of_lt hδ)
  have hhi : hi ≤ (n : ℝ) := by
    have hc : ((r + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hr
    calc
      hi ≤ (N : ℝ) * δ := mul_le_mul_of_nonneg_right hc (le_of_lt hδ)
      _ = (n : ℝ) := by dsimp [δ]; field_simp
  have hab : lo ≤ hi := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ r) (le_of_lt hδ)
  have hset : Ioo (0 : ℝ) (n : ℝ) ∩ Ico lo hi =
      Ico lo hi \ ({0} : Set ℝ) := by
    ext t
    simp only [mem_inter_iff, mem_Ioo, mem_Ico, mem_diff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨ht0, htn⟩, hcell⟩
      exact ⟨hcell, ne_of_gt ht0⟩
    · rintro ⟨⟨htlo, hthi⟩, htne⟩
      exact ⟨⟨lt_of_le_of_ne (le_trans h0 htlo) (Ne.symm htne),
        lt_of_lt_of_le hthi hhi⟩, ⟨htlo, hthi⟩⟩
  rw [show Ioo (0 : ℝ) (n : ℝ) ∩
      Ico ((r : ℝ) * δ) (((r + 1 : ℕ) : ℝ) * δ) =
      Ico lo hi \ ({0} : Set ℝ) from hset]
  have heq : volume (Ico lo hi \ ({0} : Set ℝ)) = volume (Ico lo hi) :=
    measure_diff_null (by simp)
  rw [heq, Real.volume_Ico]
  simp only [ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  have hd : hi - lo = δ := by dsimp [hi, lo]; push_cast; ring
  exact hd
