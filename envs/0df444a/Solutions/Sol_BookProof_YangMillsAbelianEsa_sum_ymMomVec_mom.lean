-- Prove2me | solution 1 for BookProof.YangMillsAbelianEsa.sum_ymMomVec_mom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:06:05.163211+00:00
-- url     : https://prove2.me/submissions/5b85f934-076c-4e66-81f6-c24a6d71f70c

-- Generated from ChapterYangMillsAbelianEsa.lean — solution of BookProof.YangMillsAbelianEsa.sum_ymMomVec_mom
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.YangMillsAbelianEsa




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (m : Fin 24) :
    ∑ n : Fin 99, ((ymMomVec m n : ℝ) : ℂ) • momPoly (d := 99) n
      = momPoly (ymMomIdx m) := by

  rw [Finset.sum_eq_single (ymMomIdx m)]
  · simp [ymMomVec]
  · intro b _ hb
    simp [ymMomVec, hb]
  · intro h
    exact absurd (Finset.mem_univ (ymMomIdx m)) h
