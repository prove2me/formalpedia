-- Prove2me | solution 1 for BookProof.ChapterSirkTrotterKato.galerkin_flow_transfer
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:41:12.099617+00:00
-- url     : https://prove2.me/submissions/c755d787-99f8-4d8c-8ead-df7eb35933ed

-- Generated from ChapterSirkTrotterKatoGalerkin.lean — solution of BookProof.ChapterSirkTrotterKato.galerkin_flow_transfer
import Mathlib
import Definitions.Def_ChapterSirkTrotterKatoGalerkin
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_flow_transfer_of_strong_tendsto
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
    (b : HilbertBasis ℕ ℂ H) (v : H) {T₀ : ℝ} (hT₀ : 0 ≤ T₀) :
    TendstoUniformlyOn
      (fun m t => (ofBounded (galerkinCompression A b m)
        (isSelfAdjoint_galerkinCompression hA b m)).stoneU t v)
      (fun t => (ofBounded A hA).stoneU t v) atTop (Set.Icc (-T₀) T₀) :=
  flow_transfer_of_strong_tendsto (fun m => isSelfAdjoint_galerkinCompression hA b m) hA
      (galerkinCompression_tendsto A b) v hT₀
