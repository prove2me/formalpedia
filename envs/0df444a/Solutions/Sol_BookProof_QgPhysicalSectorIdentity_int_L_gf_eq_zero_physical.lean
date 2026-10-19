-- Prove2me | solution 1 for BookProof.QgPhysicalSectorIdentity.int_L_gf_eq_zero_physical
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T23:59:35.977994+00:00
-- url     : https://prove2.me/submissions/a55bba97-764e-4966-8d3b-2cbac730c437

-- Generated from ChapterQgPhysicalSectorIdentity.lean — solution of BookProof.QgPhysicalSectorIdentity.int_L_gf_eq_zero_physical
import Mathlib
import Definitions.Def_ChapterQgPhysicalSectorIdentity
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterGaugeFixing
open BookProof.QgPhysicalSectorIdentity




open BookProof.GaugeFixing
open BookProof.FockQuadratic
open BookProof.OperatorSeries
open BookProof.FarisLavine
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.IkebeKato
open scoped ENNReal

variable {F : BiDegree → Type} (S : DerivativeVariableFixingSystem F)

set_option maxHeartbeats 1000000 in
theorem solution (I : BrstIntegral S.toGaugeFixingSystem) :
    I.int (sTop S.toGaugeFixingSystem (Psi S.toGaugeFixingSystem)) = 0 := I.int_of_s (Psi S.toGaugeFixingSystem)
