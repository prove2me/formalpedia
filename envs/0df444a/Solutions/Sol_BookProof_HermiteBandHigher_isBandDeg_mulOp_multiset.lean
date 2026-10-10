-- Prove2me | solution 1 for BookProof.HermiteBandHigher.isBandDeg_mulOp_multiset
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:58:42.59998+00:00
-- url     : https://prove2.me/submissions/c9805823-e2f5-49bd-ba5b-cd640ed6d910

-- Generated from ChapterHermiteBandCalculusHigher.lean — solution of BookProof.HermiteBandHigher.isBandDeg_mulOp_multiset
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Theorems.Thm_BookProof_HermiteBandHigher_IsBandR_comp
import Theorems.Thm_BookProof_HermiteBandHigher_IsBandDeg_comp
import Theorems.Thm_BookProof_HermiteBandHigher_isBandDeg1_mulXPoly
import Theorems.Thm_BookProof_HermiteBandHigher_isBandDeg_one_op
import Theorems.Thm_BookProof_HermiteBandHigher_mulOp_eq_mulXPoly
import Theorems.Thm_BookProof_HermiteBandHigher_mulOp_one
import Theorems.Thm_BookProof_HermiteBandHigher_mulOp_mul
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.HermiteBandHigher




noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.ChapterF7

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (s : Multiset (Fin d)) :
    IsBandDeg (Multiset.card s)
      (mulOp ((s.map (fun i => (X i : MvPolynomial (Fin d) ℂ))).prod)) := by

  classical
  induction s using Multiset.induction_on with
  | empty => simpa [mulOp_one] using (isBandDeg_one_op (d := d))
  | cons i s ih =>
      have hprod : ((i ::ₘ s).map (fun j => (X j : MvPolynomial (Fin d) ℂ))).prod
          = (X i : MvPolynomial (Fin d) ℂ)
              * (s.map (fun j => (X j : MvPolynomial (Fin d) ℂ))).prod := by
        simp
      rw [hprod, mulOp_mul, Multiset.card_cons]
      have := (isBandDeg1_mulXPoly (d := d) i).comp ih
      rw [mulOp_eq_mulXPoly]
      simpa [Nat.add_comm] using this
