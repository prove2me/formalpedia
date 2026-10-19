-- Prove2me | solution 1 for BookProof.QgPhysicalSectorIdentity.matrixModel_c_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:22:05.438273+00:00
-- url     : https://prove2.me/submissions/b3c37f78-fefd-4fb9-bb98-1df604a992d8

import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Mathlib
import Definitions.Def_ChapterQgPhysicalSectorIdentity
import Definitions.Def_ChapterGaugeFixing
-- Generated from ChapterQgPhysicalSectorIdentity.lean — theorem BookProof.QgPhysicalSectorIdentity.matrixModel_c_ne_zero
open BookProof.GaugeFixing
open BookProof.QgPhysicalSectorIdentity



open BookProof.GaugeFixing
open BookProof.FockQuadratic
open BookProof.OperatorSeries
open BookProof.FarisLavine
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.IkebeKato
open scoped ENNReal

variable {F : BiDegree → Type} (S : DerivativeVariableFixingSystem F)


theorem solution : (BookProof.QgPhysicalSectorIdentity.matrixModel.c : Mat2) ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun h 0) 1
  revert h1
  change (-Qm : Mat2) 0 1 = 0 → False
  simp [Qm]

