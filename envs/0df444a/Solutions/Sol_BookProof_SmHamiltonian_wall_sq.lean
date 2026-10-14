-- Prove2me | solution 1 for BookProof.SmHamiltonian.wall_sq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T10:31:14.007986+00:00
-- url     : https://prove2.me/submissions/274b2720-898c-4eda-82fe-23eed691d762

-- Generated from ChapterSmHamiltonian.lean — theorem BookProof.SmHamiltonian.wall_sq
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterSmHamiltonian
open BookProof.SmHamiltonian



open MvPolynomial
open BookProof.SmOneParticle
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension

noncomputable section

variable {D : ℕ}
open BookProof.SmHamiltonian

theorem solution(P : SmParams) (q : ℝ) :
    1 / 2 * (Real.sqrt (P.lam / 2) * (q - P.vev ^ 2)) ^ 2
      = P.lam / 4 * (q - P.vev ^ 2) ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (by linarith [P.lam_nonneg])]
  ring
