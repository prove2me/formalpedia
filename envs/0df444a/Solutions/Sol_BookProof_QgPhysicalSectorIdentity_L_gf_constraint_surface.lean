-- Prove2me | solution 1 for BookProof.QgPhysicalSectorIdentity.L_gf_constraint_surface
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T23:58:14.572981+00:00
-- url     : https://prove2.me/submissions/bb624010-537a-4365-a873-b8aedbcb40cb

-- Generated from ChapterQgPhysicalSectorIdentity.lean — solution of BookProof.QgPhysicalSectorIdentity.L_gf_constraint_surface
import Mathlib
import Definitions.Def_ChapterQgPhysicalSectorIdentity
import Theorems.Thm_BookProof_QgPhysicalSectorIdentity_lagrange_term_zero_of_fixing
import Theorems.Thm_BookProof_GaugeFixing_L_gf_evaluation
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
    S.s (Psi S.toGaugeFixingSystem) =
      S.sub (2, 0) (S.zero (2, 0)) (S.mul (1, -1) (1, 1) S.c_bar S.c) := by

  rw [L_gf_evaluation (S := S.toGaugeFixingSystem), lagrange_term_zero_of_fixing S hfix]
