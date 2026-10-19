-- Prove2me | solution 1 for BookProof.QgPhysicalSectorIdentity.coupling_weighted_summable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:00:16.891128+00:00
-- url     : https://prove2.me/submissions/5e264592-5e13-4317-a861-27217c999ed9

-- Generated from ChapterQgPhysicalSectorIdentity.lean — solution of BookProof.QgPhysicalSectorIdentity.coupling_weighted_summable
import Mathlib
import Definitions.Def_ChapterQgPhysicalSectorIdentity
import Theorems.Thm_BookProof_QgPhysicalSectorIdentity_wsum_creIdx
import Theorems.Thm_BookProof_QgPhysicalSectorIdentity_wsum_annIdx
import Definitions.Def_ChapterGaugeFixing
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.QgPhysicalSectorIdentity




open BookProof.GaugeFixing
open BookProof.FockQuadratic
open BookProof.OperatorSeries
open BookProof.FarisLavine
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.IkebeKato
open scoped ENNReal

variable {F : BiDegree → Type} (S : DerivativeVariableFixingSystem F)
variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {ω : ι → ℝ} (h : ι × ι → ℂ)
    (hsum : Summable fun k : ι × ι => ‖h k‖ * (ω k.1 + ω k.2 + 2)) :
    Summable fun k : ι × ι => ‖h k‖ * (wsum ω (creIdx k.1) + wsum ω (annIdx k.2) + 2) := by

  refine hsum.congr ?_
  intro k
  rw [wsum_creIdx, wsum_annIdx]
