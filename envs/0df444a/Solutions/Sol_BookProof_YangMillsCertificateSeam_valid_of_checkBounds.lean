-- Prove2me | solution 1 for BookProof.YangMillsCertificateSeam.valid_of_checkBounds
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T13:26:45.383251+00:00
-- url     : https://prove2.me/submissions/69a451ca-c4d3-42f2-aa27-51ac196fdaa2

-- Generated from ChapterYangMillsCertificateSeam.lean — solution of BookProof.YangMillsCertificateSeam.valid_of_checkBounds
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
open BookProof.YangMillsCertificateSeam



noncomputable section


open BookProof.SirkCertificateReader
open BookProof.SchurGershgorin
open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.TruncationGapLift
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain

set_option maxHeartbeats 1000000 in

theorem solution {c : MatrixBoundRecord} (h : c.checkBounds = true) : c.Valid := by
  rw [MatrixBoundRecord.checkBounds, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨by simpa using h.1.1, by simpa using h.1.2, by simpa using h.2⟩

/-! ## 3. The seam -/
