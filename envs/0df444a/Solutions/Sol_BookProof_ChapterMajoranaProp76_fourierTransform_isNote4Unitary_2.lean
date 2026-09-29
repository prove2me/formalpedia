-- Prove2me | solution 2 for BookProof.ChapterMajoranaProp76.fourierTransform_isNote4Unitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T06:01:16.264314+00:00
-- url     : https://prove2.me/submissions/afdf64c1-45c7-430d-ad1d-cdf5a6d802cb

-- Generated from ChapterMajoranaProp76.lean — solution of BookProof.ChapterMajoranaProp76.fourierTransform_isNote4Unitary
import Mathlib
import Definitions.Def_ChapterMajoranaProp76
import Theorems.Thm_BookProof_ChapterMajoranaProp76_LinearIsometryEquiv_isNote4Unitary
open BookProof.ChapterMajoranaProp76











open scoped InnerProductSpace


variable {𝕜 : Type*} [RCLike 𝕜]


variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
  [NormedAddCommGroup L] [InnerProductSpace 𝕜 L]






variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]






open MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution :
    IsNote4Unitary ℂ (Lp.fourierTransformₗᵢ E F : Lp F 2 volume → Lp F 2 volume) := LinearIsometryEquiv.isNote4Unitary (Lp.fourierTransformₗᵢ E F)
