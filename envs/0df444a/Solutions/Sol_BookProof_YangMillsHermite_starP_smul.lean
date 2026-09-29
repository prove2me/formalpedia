-- Prove2me | solution 1 for BookProof.YangMillsHermite.starP_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:32:49.776144+00:00
-- url     : https://prove2.me/submissions/76eb83d6-da5f-4c7b-8330-8971fecec6bd

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.starP_smul
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
import Theorems.Thm_BookProof_YangMillsHermite_starP_mul
import Theorems.Thm_BookProof_YangMillsHermite_starP_C
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (c : ℂ) (p : MvPolynomial (Fin d) ℂ) :
    starP (c • p) = ((starRingEnd ℂ) c) • starP p := by

  rw [smul_eq_C_mul, starP_mul, starP_C, smul_eq_C_mul]
