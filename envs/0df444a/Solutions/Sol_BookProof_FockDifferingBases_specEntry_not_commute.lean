-- Prove2me | solution 1 for BookProof.FockDifferingBases.specEntry_not_commute
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T04:57:10.161905+00:00
-- url     : https://prove2.me/submissions/99df47d1-efe1-4abf-88f9-8136e2480f81

-- Generated from ChapterFockDifferingBasesEsa.lean — solution of BookProof.FockDifferingBases.specEntry_not_commute
import Mathlib
import Definitions.Def_ChapterFockDifferingBasesEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterFockQuadraticEsa
open BookProof.FockDifferingBases




open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries BookProof.FockQuadratic

noncomputable section

variable {ι κ : Type*} {ω : ι → ℝ}

variable {ι κ : Type*} {ω : ι → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution :
    matMul (specEntry (1 : ℝ) (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0))
        (specEntry (1 : ℝ) (fun _ : Fin 2 => (1 : ℂ)))
      ≠ matMul (specEntry (1 : ℝ) (fun _ : Fin 2 => (1 : ℂ)))
        (specEntry (1 : ℝ) (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0)) := by

  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [matMul, specEntry] at h01
