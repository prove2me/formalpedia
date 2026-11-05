-- Prove2me | solution 1 for BookProof.HermiteLadder.gaussInt_sub_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T14:55:59.051225+00:00
-- url     : https://prove2.me/submissions/264412a7-7bc6-4283-8068-f8e431f63a51

-- Generated from ChapterHermiteLadderOrder.lean — solution of BookProof.HermiteLadder.gaussInt_sub'
import Mathlib
import Definitions.Def_ChapterHermiteLadderOrder
import Theorems.Thm_BookProof_QgHermiteFriedrichs_gaussInt_neg
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterDegSchrodingerCore
open BookProof.HermiteLadder




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.DegSchrodinger
open scoped ENNReal
open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by

  rw [sub_eq_add_neg, gaussInt_add, gaussInt_neg, ← sub_eq_add_neg]
