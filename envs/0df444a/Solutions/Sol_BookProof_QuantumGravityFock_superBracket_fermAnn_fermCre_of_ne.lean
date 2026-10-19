-- Prove2me | solution 1 for BookProof.QuantumGravityFock.superBracket_fermAnn_fermCre_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:06:46.982645+00:00
-- url     : https://prove2.me/submissions/baed9efe-525c-4ee8-89eb-c13c2c913959

-- Generated from ChapterQuantumGravityFock.lean — solution of BookProof.QuantumGravityFock.superBracket_fermAnn_fermCre_of_ne
import Mathlib
import Definitions.Def_ChapterQuantumGravityFock
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.QuantumGravityFock




open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {j k : ℕ} (h : j ≠ k) :
    superBracket 1 1 (fermAnn j) (fermCre k) = 0 := by

  refine LinearMap.ext fun u => ?_
  rw [superBracket_odd_odd, car_fermAnn_fermCre_of_ne h]
  rfl
