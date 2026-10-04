-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockManyMode.fockH_relative_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:33:22.209471+00:00
-- url     : https://prove2.me/submissions/4f470e17-2fe5-439d-9c90-c6d9a387ecbd

-- Generated from ChapterNavierStokesFockManyMode.lean — solution of BookProof.NavierStokesFlow.FockManyMode.fockH_relative_bound
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
import Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_fockH_apply
import Theorems.Thm_BookProof_NavierStokesFlow_ShiftHamiltonian_ShiftData_shiftH_relative_bound
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian


variable {d : ℕ} {κ : Fin d → ℝ}

variable {d : ℕ} {κ : Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hκ : ∀ i, 0 ≤ κ i) (x : maxDom (fockSym κ)) :
    ‖(fockH hκ x : L2I (Occ d))‖ ^ 2
      ≤ ((d : ℝ) ^ 2 / 2) * ‖(diagMax (fockSym κ) x : L2I (Occ d))‖ ^ 2
        + (2 * d * ∑ i, κ i ^ 2) * ‖(x : L2I (Occ d))‖ ^ 2 := by

  have hmode : ∀ i : Fin d,
      ‖(ShiftData.shiftH (modeData hκ i) x : L2I (Occ d))‖ ^ 2
        ≤ (1 / 2) * ‖(diagMax (fockSym κ) x : L2I (Occ d))‖ ^ 2
          + (2 * κ i ^ 2) * ‖(x : L2I (Occ d))‖ ^ 2 := by
    intro i
    have h := ShiftData.shiftH_relative_bound (modeData hκ i) x
    have hK : 8 * ((modeData hκ i).K) ^ 2 = 2 * κ i ^ 2 := by
      simp only [modeData]
      ring
    rw [hK] at h
    exact h
  have htri : ‖(fockH hκ x : L2I (Occ d))‖
      ≤ ∑ i, ‖(ShiftData.shiftH (modeData hκ i) x : L2I (Occ d))‖ := by
    rw [fockH_apply]
    exact norm_sum_le _ _
  have hsq : ‖(fockH hκ x : L2I (Occ d))‖ ^ 2
      ≤ (∑ i, ‖(ShiftData.shiftH (modeData hκ i) x : L2I (Occ d))‖) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖(fockH hκ x : L2I (Occ d))‖ := norm_nonneg _
    nlinarith [htri, h0]
  have hcs : (∑ i, ‖(ShiftData.shiftH (modeData hκ i) x : L2I (Occ d))‖) ^ 2
      ≤ (d : ℝ) * ∑ i, ‖(ShiftData.shiftH (modeData hκ i) x : L2I (Occ d))‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => ‖(ShiftData.shiftH (modeData hκ i) x : L2I (Occ d))‖)
    simpa using h
  have hsum : (∑ i, ‖(ShiftData.shiftH (modeData hκ i) x : L2I (Occ d))‖ ^ 2)
      ≤ ((d : ℝ) / 2) * ‖(diagMax (fockSym κ) x : L2I (Occ d))‖ ^ 2
        + (2 * ∑ i, κ i ^ 2) * ‖(x : L2I (Occ d))‖ ^ 2 := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hmode i)
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul] at h
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    calc (∑ i, ‖(ShiftData.shiftH (modeData hκ i) x : L2I (Occ d))‖ ^ 2)
        ≤ ((d : ℝ) * (1 / 2)) * ‖(diagMax (fockSym κ) x : L2I (Occ d))‖ ^ 2
            + (∑ i, 2 * κ i ^ 2) * ‖(x : L2I (Occ d))‖ ^ 2 := h
      _ = ((d : ℝ) / 2) * ‖(diagMax (fockSym κ) x : L2I (Occ d))‖ ^ 2
            + (2 * ∑ i, κ i ^ 2) * ‖(x : L2I (Occ d))‖ ^ 2 := by
          rw [← Finset.mul_sum]
          ring
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  nlinarith [hsq, hcs, hsum, sq_nonneg ‖(diagMax (fockSym κ) x : L2I (Occ d))‖,
    sq_nonneg ‖(x : L2I (Occ d))‖]
