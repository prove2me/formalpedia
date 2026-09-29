-- Prove2me | solution 2 for BookProof.ChapterMajoranaProp76.energyTransform_unitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:28:54.539144+00:00
-- url     : https://prove2.me/submissions/ec165be3-fac5-46e5-a2b6-2d9f5a8e10ce

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
