-- Prove2me | solution 1 for BookProof.YangMillsHermite.ymHamiltonian_quadForm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T04:21:02.151996+00:00
-- url     : https://prove2.me/submissions/636b2c64-fc0c-4579-bb21-aa48f342b5cc

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.ymHamiltonian_quadForm
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
theorem solution (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (x : D) :
    quadForm (ymHamiltonian Φ fabc) x
      = 1 / 2 * (∑ m, ‖((piOps Φ m x : D) : L2d 99)‖ ^ 2)
        + 1 / 2 * ∑ m, ‖((magOps Φ fabc m x : D) : L2d 99)‖ ^ 2 := weylOpDom_quadForm (piOps_symmetricOn Φ) (magOps_symmetricOn Φ fabc) x
