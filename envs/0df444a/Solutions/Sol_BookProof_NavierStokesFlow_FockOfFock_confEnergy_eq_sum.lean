-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.confEnergy_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:24:58.009845+00:00
-- url     : https://prove2.me/submissions/a1a5827b-43d7-4bac-930a-eaa5ca1b5d17

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.confEnergy_eq_sum
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock



open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]

set_option maxHeartbeats 1000000 in
theorem solution {ω : M → ℝ} {n : Conf M} {S : Finset M} (hS : n.support ⊆ S) :
    confEnergy ω n = ∑ m ∈ S, (n m : ℝ) * ω m :=
  Finset.sum_subset hS fun m _ hm => by
      have hn : n m = 0 := by simpa using hm
      simp [hn]
