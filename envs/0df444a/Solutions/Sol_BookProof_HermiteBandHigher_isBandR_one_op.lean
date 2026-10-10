-- Prove2me | solution 1 for BookProof.HermiteBandHigher.isBandR_one_op
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:56:26.888972+00:00
-- url     : https://prove2.me/submissions/27b40df0-5fe6-4cca-87a6-cabd301f6591

-- Generated from ChapterHermiteBandCalculusHigher.lean — solution of BookProof.HermiteBandHigher.isBandR_one_op
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBandHigher




noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteBand

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution :
    IsBandR 0 0 (LinearMap.id : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) := by

  classical
  refine ⟨1, 1, zero_le_one, fun α => ⟨Finsupp.single α 1, ?_, ?_, ?_, ?_⟩⟩
  · rw [hcomb, Finsupp.linearCombination_single]
    simp
  · exact le_trans (Finset.card_le_card Finsupp.support_single_subset) (by simp)
  · intro β hβ
    have hβ' : β = α := Finset.mem_singleton.mp (Finsupp.support_single_subset hβ)
    subst hβ'
    simp
  · intro β
    rw [Finsupp.single_apply]
    split <;> simp [gpow]
