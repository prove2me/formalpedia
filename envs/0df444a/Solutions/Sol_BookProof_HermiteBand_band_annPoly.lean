-- Prove2me | solution 1 for BookProof.HermiteBand.band_annPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T12:07:58.499033+00:00
-- url     : https://prove2.me/submissions/e2ef4caf-d0aa-4e5e-ad70-dd31ee96429e

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.band_annPoly
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Theorems.Thm_BookProof_HermiteBand_annPoly_hpsi
import Theorems.Thm_BookProof_HermiteBand_degree_sub_single
import Theorems.Thm_BookProof_HermiteBand_le_degree
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteBand








noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) : Band (annPoly i) 1 1 1 g1 := by

  classical
  intro α
  refine ⟨Finsupp.single (α - Finsupp.single i 1)
      ((Real.sqrt (α i : ℝ) : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · rw [annPoly_hpsi, hcomb, Finsupp.linearCombination_single]
  · exact le_trans (Finset.card_le_card Finsupp.support_single_subset) (by simp)
  · intro β hβ
    have hβ' : β = α - Finsupp.single i 1 :=
      Finset.mem_singleton.mp (Finsupp.support_single_subset hβ)
    have hne : ((Real.sqrt (α i : ℝ) : ℝ) : ℂ) ≠ 0 := by
      intro h0
      rw [h0] at hβ
      simp at hβ
    have hpos : 1 ≤ α i := by
      rcases Nat.eq_zero_or_pos (α i) with h0 | h
      · exfalso; apply hne; rw [h0]; simp
      · exact h
    subst hβ'
    have := degree_sub_single (α := α) (i := i) hpos
    omega
  · intro β
    have hb : ‖(Finsupp.single (α - Finsupp.single i 1)
        ((Real.sqrt (α i : ℝ) : ℝ) : ℂ) : (Fin d →₀ ℕ) →₀ ℂ) β‖
          ≤ Real.sqrt (α i : ℝ) := by
      rw [Finsupp.single_apply]
      split
      · simp [abs_of_nonneg (Real.sqrt_nonneg (α i : ℝ))]
      · simp [Real.sqrt_nonneg]
    refine le_trans hb ?_
    rw [one_mul, g1]
    exact Real.sqrt_le_sqrt (by
      have := le_degree α i
      have : (α i : ℝ) ≤ (α.degree : ℝ) := by exact_mod_cast this
      linarith)
