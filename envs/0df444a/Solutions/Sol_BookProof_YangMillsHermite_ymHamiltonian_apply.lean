-- Prove2me | solution 1 for BookProof.YangMillsHermite.ymHamiltonian_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T03:53:48.2679+00:00
-- url     : https://prove2.me/submissions/a9a89049-3490-491e-b0c7-25b855c559e7

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.ymHamiltonian_apply
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
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
    ymHamiltonian Φ fabc x
      = ((1 / 2 : ℝ) : ℂ)
        • ((∑ m, ((piOps Φ m (piOps Φ m x) : D) : L2d 99))
            + ∑ m, ((magOps Φ fabc m (magOps Φ fabc m x) : D) : L2d 99)) := weylOp_apply _ _ x
