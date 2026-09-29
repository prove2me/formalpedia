-- Prove2me | solution 1 for BookProof.ChapterMajoranaProp76.energyTransform_fourier_unitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:35:42.723675+00:00
-- url     : https://prove2.me/submissions/c24de2d8-77ae-455f-b600-7299c636971c

-- Generated from ChapterMajoranaProp76.lean — solution of BookProof.ChapterMajoranaProp76.energyTransform_fourier_unitary
import Mathlib
import Definitions.Def_ChapterMajoranaProp76
import Theorems.Thm_BookProof_ChapterMajoranaProp76_energyTransform_unitary
import Theorems.Thm_BookProof_ChapterMajoranaProp76_fourierTransform_isNote4Unitary
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
theorem solution {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (Θ : Lp F 2 volume ≃ₗᵢ[ℂ] K) :
    IsNote4Unitary ℂ (energyTransform Θ (Lp.fourierTransformₗᵢ E F)) := energyTransform_unitary Θ fourierTransform_isNote4Unitary
