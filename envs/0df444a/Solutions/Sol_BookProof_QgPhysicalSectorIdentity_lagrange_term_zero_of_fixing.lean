-- Prove2me | solution 1 for BookProof.QgPhysicalSectorIdentity.lagrange_term_zero_of_fixing
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T23:58:13.380986+00:00
-- url     : https://prove2.me/submissions/8d35acb9-2b64-45fd-a256-bbecdfbd5af5

-- Generated from ChapterQgPhysicalSectorIdentity.lean — solution of BookProof.QgPhysicalSectorIdentity.lagrange_term_zero_of_fixing
import Mathlib
import Definitions.Def_ChapterQgPhysicalSectorIdentity
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterGaugeFixing
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.QgPhysicalSectorIdentity




open BookProof.GaugeFixing
open BookProof.FockQuadratic
open BookProof.OperatorSeries
open BookProof.FarisLavine
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.IkebeKato
open scoped ENNReal
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval

variable {F : BiDegree → Type} (S : DerivativeVariableFixingSystem F)

set_option maxHeartbeats 1000000 in
theorem solution
    (hfix : gaugeField S.toGaugeFixingSystem = S.toGaugeFixingSystem.zero (1, 0)) :
    S.mul (1, 0) (1, 0) S.B (gaugeField S.toGaugeFixingSystem) = S.zero (2, 0) := by

  rw [hfix]
  exact S.mul_zero_right S.B
