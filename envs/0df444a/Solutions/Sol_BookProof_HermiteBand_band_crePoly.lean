-- Prove2me | solution 1 for BookProof.HermiteBand.band_crePoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T12:32:47.566052+00:00
-- url     : https://prove2.me/submissions/3b6fc13d-a47c-4c24-9903-cc64d5d7dd74

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.band_crePoly
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Theorems.Thm_BookProof_HermiteBand_crePoly_hpsi
import Theorems.Thm_BookProof_HermiteBand_degree_add_single
import Theorems.Thm_BookProof_HermiteBand_le_degree
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteBand








noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) : Band (crePoly i) 1 1 1 g1 := by

  classical
  intro α
  refine ⟨Finsupp.single (α + Finsupp.single i 1)
      ((Real.sqrt ((α i : ℝ) + 1) : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · rw [crePoly_hpsi, hcomb, Finsupp.linearCombination_single]
  · exact le_trans (Finset.card_le_card Finsupp.support_single_subset) (by simp)
  · intro β hβ
    have hβ' : β = α + Finsupp.single i 1 :=
      Finset.mem_singleton.mp (Finsupp.support_single_subset hβ)
    subst hβ'
    rw [degree_add_single]
    omega
  · intro β
    have hb : ‖(Finsupp.single (α + Finsupp.single i 1)
        ((Real.sqrt ((α i : ℝ) + 1) : ℝ) : ℂ) : (Fin d →₀ ℕ) →₀ ℂ) β‖
          ≤ Real.sqrt ((α i : ℝ) + 1) := by
      rw [Finsupp.single_apply]
      split
      · simp [abs_of_nonneg (Real.sqrt_nonneg ((α i : ℝ) + 1))]
      · simp [Real.sqrt_nonneg]
    refine le_trans hb ?_
    rw [one_mul, g1]
    exact Real.sqrt_le_sqrt (by
      have := le_degree α i
      have : (α i : ℝ) ≤ (α.degree : ℝ) := by exact_mod_cast this
      linarith)
