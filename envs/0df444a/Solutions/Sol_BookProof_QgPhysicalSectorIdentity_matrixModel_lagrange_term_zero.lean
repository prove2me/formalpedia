-- Prove2me | solution 1 for BookProof.QgPhysicalSectorIdentity.matrixModel_lagrange_term_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:22:21.856618+00:00
-- url     : https://prove2.me/submissions/86b7860d-befa-47cf-8c20-a93522cdb7fb

import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Mathlib
import Definitions.Def_ChapterQgPhysicalSectorIdentity
import Definitions.Def_ChapterGaugeFixing
import Definitions.Def_ChapterSirkFinitePrecision
-- Generated from ChapterQgPhysicalSectorIdentity.lean — theorem BookProof.QgPhysicalSectorIdentity.matrixModel_lagrange_term_zero
open BookProof.GaugeFixing
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.QgPhysicalSectorIdentity



open BookProof.GaugeFixing
open BookProof.FockQuadratic
open BookProof.OperatorSeries
open BookProof.FarisLavine
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.IkebeKato
open scoped ENNReal

variable {F : BiDegree → Type} (S : DerivativeVariableFixingSystem F)


theorem solution
    (hfix : gaugeField BookProof.QgPhysicalSectorIdentity.matrixModel.toGaugeFixingSystem = 0) :
    BookProof.QgPhysicalSectorIdentity.matrixModel.mul (1, 0) (1, 0) BookProof.QgPhysicalSectorIdentity.matrixModel.B
        (gaugeField BookProof.QgPhysicalSectorIdentity.matrixModel.toGaugeFixingSystem) = 0 := by
  rw [hfix]
  exact Matrix.mul_zero _

