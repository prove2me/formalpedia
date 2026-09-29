-- Prove2me | solution 1 for BookProof.YangMillsHermite.starP_real_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:36:32.910995+00:00
-- url     : https://prove2.me/submissions/ebcf081a-1d93-4b88-bcbf-b89fb4b55655

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.starP_real_smul
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
import Theorems.Thm_BookProof_YangMillsHermite_starP_smul
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) (p : MvPolynomial (Fin d) ℂ) :
    starP ((t : ℂ) • p) = (t : ℂ) • starP p := by

  rw [starP_smul, Complex.conj_ofReal]
