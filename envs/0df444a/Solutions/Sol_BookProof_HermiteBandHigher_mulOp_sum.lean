-- Prove2me | solution 1 for BookProof.HermiteBandHigher.mulOp_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T02:12:26.029203+00:00
-- url     : https://prove2.me/submissions/fc03d860-feda-4361-8b3c-68c27f732540

-- Generated from ChapterHermiteBandCalculusHigher.lean — solution of BookProof.HermiteBandHigher.mulOp_sum
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Theorems.Thm_BookProof_HermiteBandHigher_mulOp_add_prime
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterF7
open BookProof.HermiteBandHigher




noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial (Fin d) ℂ) :
    mulOp (∑ i ∈ s, F i) = ∑ i ∈ s, mulOp (F i) := by

  classical
  induction s using Finset.induction_on with
  | empty => refine LinearMap.ext fun p => ?_; simp [mulOp]
  | insert a s ha ih => rw [Finset.sum_insert ha, mulOp_add_prime, ih, Finset.sum_insert ha]
