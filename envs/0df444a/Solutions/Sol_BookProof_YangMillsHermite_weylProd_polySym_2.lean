-- Prove2me | solution 2 for BookProof.YangMillsHermite.weylProd_polySym
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T05:00:32.097887+00:00
-- url     : https://prove2.me/submissions/84699373-9032-4231-ba21-3c1f57abef7a

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.weylProd_polySym
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
import Theorems.Thm_BookProof_YangMillsHermite_PolySym_real_smul
import Theorems.Thm_BookProof_YangMillsHermite_PolyAdj_symm_of
import Theorems.Thm_BookProof_YangMillsHermite_PolySym_comp_adj
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hS : PolySym S) (hT : PolySym T) : PolySym (weylProd S T) := PolySym.real_smul ((hS.comp_adj hT).symm_of (hT.comp_adj hS))
