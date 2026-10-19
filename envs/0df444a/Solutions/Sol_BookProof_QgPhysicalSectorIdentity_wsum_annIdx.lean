-- Prove2me | solution 1 for BookProof.QgPhysicalSectorIdentity.wsum_annIdx
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:00:15.215005+00:00
-- url     : https://prove2.me/submissions/d5616597-b917-4591-8bc8-4476844029e3

-- Generated from ChapterQgPhysicalSectorIdentity.lean — solution of BookProof.QgPhysicalSectorIdentity.wsum_annIdx
import Mathlib
import Definitions.Def_ChapterQgPhysicalSectorIdentity
import Theorems.Thm_BookProof_FockQuadratic_wsum_single
import Definitions.Def_ChapterGaugeFixing
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterA3n
open BookProof.QgPhysicalSectorIdentity




open BookProof.GaugeFixing
open BookProof.FockQuadratic
open BookProof.OperatorSeries
open BookProof.FarisLavine
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.IkebeKato
open scoped ENNReal
open BookProof.ChapterA3n

variable {F : BiDegree → Type} (S : DerivativeVariableFixingSystem F)
variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (ω : ι → ℝ) (j : ι) : wsum ω (annIdx j) = ω j := by

  rw [annIdx, wsum_single]
  ring
