-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockLagrangian.tailStep_subset
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T21:05:09.980094+00:00
-- url     : https://prove2.me/submissions/6e66e070-1f44-4a56-8ee2-b55731b4f5e8

-- Generated from ChapterNavierStokesFockParcels.lean — solution of BookProof.NavierStokesFlow.FockLagrangian.tailStep_subset
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian



open MeasureTheory



open FullEsa FockContinuum

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) : tailStep k ⊆ tailFockSet := Set.image_mono fun _ hξ i _ => Set.mem_iUnion.2 ⟨k, hξ i (Set.mem_univ i)⟩
