-- Prove2me | solution 1 for BookProof.HermiteBandHigher.isBandDeg_mulOp_monomial
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:59:17.787046+00:00
-- url     : https://prove2.me/submissions/0aed72c0-1671-4154-9be1-0d2b17d34eef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterHermiteBandCalculusHigher.lean — solution of BookProof.HermiteBandHigher.isBandDeg_mulOp_monomial
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Theorems.Thm_BookProof_HermiteBandHigher_IsBandR_smul
import Theorems.Thm_BookProof_HermiteBandHigher_IsBandDeg_smul
import Theorems.Thm_BookProof_HermiteBandHigher_mulOp_smul
import Theorems.Thm_BookProof_HermiteBandHigher_isBandDeg_mulOp_multiset
import Theorems.Thm_BookProof_HermiteBandHigher_prod_toMultiset_X
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
open BookProof.ChapterF7

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (s : Fin d →₀ ℕ) (c : ℂ) :
    IsBandDeg s.degree (mulOp (monomial s c : MvPolynomial (Fin d) ℂ)) := by

  classical
  have hmon : (monomial s c : MvPolynomial (Fin d) ℂ)
      = c • ((s.toMultiset.map (fun i => (X i : MvPolynomial (Fin d) ℂ))).prod) := by
    rw [prod_toMultiset_X, MvPolynomial.monomial_eq, smul_eq_C_mul]
  have hcard : Multiset.card s.toMultiset = s.degree := by
    rw [Finsupp.card_toMultiset]
    simp [Finsupp.degree, Finsupp.sum]
    first | rfl | done
  rw [hmon, mulOp_smul]
  exact IsBandDeg.smul c (hcard ▸ isBandDeg_mulOp_multiset s.toMultiset)
