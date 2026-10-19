-- Prove2me | solution 1 for BookProof.NavierStokesFlow.BilinearEsa.bilFun_embFun
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:23:51.998337+00:00
-- url     : https://prove2.me/submissions/565ddaba-16dd-4d07-923b-da7654dabc77

-- Generated from ChapterNavierStokesBilinearEsa.lean — solution of BookProof.NavierStokesFlow.BilinearEsa.bilFun_embFun
import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

variable {J : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (κ : J → ℝ) (j : J) (a : ℕ → ℂ) :
    bilFun κ (embFun j a) = embFun j (hFun (κ j) a) := by

  funext p
  obtain ⟨m, j'⟩ := p
  by_cases hj : j' = j
  · subst hj
    simp [bilFun, embFun]
  · simp only [bilFun, embFun, hFun, shift2, hj, if_false]
    simp
