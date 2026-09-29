-- Prove2me | solution 4 for BookProof.ChapterMajoranaProp76.energyTransform_unitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T03:16:45.299401+00:00
-- url     : https://prove2.me/submissions/65b22029-8e83-4f5e-b8fd-42ccd743d301

-- Generated from ChapterMajoranaProp76.lean — solution of BookProof.ChapterMajoranaProp76.energyTransform_unitary
import Mathlib
import Definitions.Def_ChapterMajoranaProp76
import Theorems.Thm_BookProof_ChapterMajoranaProp76_note4_conj
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

set_option maxHeartbeats 1000000 in
theorem solution (Θ : H ≃ₗᵢ[𝕜] K) {V : H → H}
    (hV : IsNote4Unitary 𝕜 V) : IsNote4Unitary 𝕜 (energyTransform Θ V) := note4_conj Θ hV
