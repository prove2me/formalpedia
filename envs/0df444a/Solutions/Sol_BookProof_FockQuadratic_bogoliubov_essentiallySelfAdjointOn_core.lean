-- Prove2me | solution 1 for BookProof.FockQuadratic.bogoliubov_essentiallySelfAdjointOn_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-13T05:05:14.620974+00:00
-- url     : https://prove2.me/submissions/2583606d-d05b-4e67-a630-9b5542605a7b

-- Generated from ChapterFockQuadraticEsa.lean — solution of BookProof.FockQuadratic.bogoliubov_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
import Theorems.Thm_BookProof_FockQuadratic_fockH_essentiallySelfAdjointOn_core
import Theorems.Thm_BookProof_FockQuadratic_wsum_pairIdx
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.FockQuadratic



open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries
open BookProof.ChapterA3n
open BookProof.DirectSumEsa
open BookProof.NavierStokesFlow.IkebeKato

noncomputable section

variable {ι : Type*}

variable {ι : Type*}
variable {ω : ι → ℝ}
variable {κ : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (hω : ∀ i, 0 ≤ ω i) (m n : κ → ι) (g : κ → ℂ)
    (hsum : Summable fun k => ‖g k‖ * (ω (m k) + ω (n k) + 2)) :
    EssentiallySelfAdjointOn (lpFiniteModes (Idx ι))
      ((fockH hω (fun k => pairIdx (m k) (n k)) (fun _ => (0 : Idx ι)) g
          (fun k => by simp)
          (by
            refine hsum.congr fun k => ?_
            simp [wsum_pairIdx])).comp
        (Submodule.inclusion (finiteModes_le_maxDom (sig ω)))) := fockH_essentiallySelfAdjointOn_core hω _ _ g _ _
