-- Prove2me | solution 1 for BookProof.ChapterSirkTrotterKato.galerkin_flow_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:41:11.352878+00:00
-- url     : https://prove2.me/submissions/6cd4ef55-6a1d-48f3-8808-c308cca1c8d0

-- Generated from ChapterSirkTrotterKatoGalerkin.lean — solution of BookProof.ChapterSirkTrotterKato.galerkin_flow_tendsto
import Mathlib
import Definitions.Def_ChapterSirkTrotterKatoGalerkin
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_flow_tendsto_of_strong_tendsto
import Theorems.Thm_BookProof_HermiteGalerkin_isSelfAdjoint_galerkinCompression
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Theorems.Thm_BookProof_HermiteGalerkin_galerkinCompression_tendsto
open BookProof.ChapterSirkTrotterKato









noncomputable section

open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterUnitaryTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]










open BookProof.HermiteGalerkin

set_option maxHeartbeats 1000000 in
theorem solution {A : H →L[ℂ] H} (hA : IsSelfAdjoint A)
    (b : HilbertBasis ℕ ℂ H) (v : H) (t : ℝ) :
    Tendsto (fun m => (ofBounded (galerkinCompression A b m)
      (isSelfAdjoint_galerkinCompression hA b m)).stoneU t v) atTop
      (𝓝 ((ofBounded A hA).stoneU t v)) :=
  flow_tendsto_of_strong_tendsto (fun m => isSelfAdjoint_galerkinCompression hA b m) hA
      (galerkinCompression_tendsto A b) v t
