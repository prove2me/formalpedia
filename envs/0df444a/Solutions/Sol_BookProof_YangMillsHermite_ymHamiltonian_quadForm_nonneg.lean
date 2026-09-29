-- Prove2me | solution 1 for BookProof.YangMillsHermite.ymHamiltonian_quadForm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:46:48.098509+00:00
-- url     : https://prove2.me/submissions/e58f6348-fef0-4f81-b75d-4e83939109d3

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.ymHamiltonian_quadForm_nonneg
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
import Theorems.Thm_BookProof_YangMillsHermite_piOps_symmetricOn
import Theorems.Thm_BookProof_YangMillsHermite_magOps_symmetricOn
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

















































variable {D : Submodule ℂ (L2d d)}












variable {D : Submodule ℂ (L2d 99)}

set_option maxHeartbeats 1000000 in
theorem solution (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (x : D) : 0 ≤ quadForm (ymHamiltonian Φ fabc) x := weylOpDom_quadForm_nonneg (piOps_symmetricOn Φ) (magOps_symmetricOn Φ fabc) x
