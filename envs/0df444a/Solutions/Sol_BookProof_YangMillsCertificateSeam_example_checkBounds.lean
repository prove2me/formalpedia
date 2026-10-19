-- Prove2me | solution 1 for BookProof.YangMillsCertificateSeam.example_checkBounds
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T13:26:49.239452+00:00
-- url     : https://prove2.me/submissions/48c31083-4c89-4fa3-abae-404ee32a9762

-- Generated from ChapterYangMillsCertificateSeam.lean — solution of BookProof.YangMillsCertificateSeam.example_checkBounds
import Mathlib
import Definitions.Def_ChapterYangMillsCertificateSeam
import Definitions.Def_ChapterSirkCertificateReader
import Definitions.Def_ChapterSchurGershgorinGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterTruncationGapLift
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFockGapChain
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.YangMillsCertificateSeam



noncomputable section


open BookProof.SirkCertificateReader
open BookProof.SchurGershgorin
open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.TruncationGapLift
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain
open BookProof.ChapterElectroweakFieldStrength

variable (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)

set_option maxHeartbeats 1000000 in

theorem solution : exampleRecord.checkBounds = true := by
  rw [MatrixBoundRecord.checkBounds]
  norm_num [MatrixBoundRecord.epsQ, MatrixBoundRecord.muQ, MatrixBoundRecord.dminQ,
    MatrixBoundRecord.rmaxQ, exampleRecord, Decimal.toQ]
