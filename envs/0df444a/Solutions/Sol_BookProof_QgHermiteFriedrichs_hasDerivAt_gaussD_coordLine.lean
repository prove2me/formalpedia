-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.hasDerivAt_gaussD_coordLine
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:20:49.182686+00:00
-- url     : https://prove2.me/submissions/8718b585-9166-48c9-b9d5-74aa987cbca9

-- Generated from ChapterQgHermiteFriedrichs.lean — solution of BookProof.QgHermiteFriedrichs.hasDerivAt_gaussD_coordLine
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Theorems.Thm_BookProof_QgHermiteFriedrichs_hasDerivAt_normSq_coordLine
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavine
open BookProof.QgHermiteFriedrichs








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}































variable (W : Vd d → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (x : Vd d) (j : Fin d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gaussD (coordLine x j s))
      (-(t / 2) * gaussD (coordLine x j t)) t := by

  have h : HasDerivAt (fun s : ℝ => -‖coordLine x j s‖ ^ 2 / 4) (-(2 * t) / 4) t :=
    ((hasDerivAt_normSq_coordLine x j t).neg).div_const 4
  have hexp := h.exp
  refine hexp.congr_deriv ?_
  rw [gaussD]
  ring
