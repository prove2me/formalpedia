-- Prove2me | solution 2 for BookProof.ChapterMajoranaProp76.energyMomentum_unitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:34:21.041178+00:00
-- url     : https://prove2.me/submissions/6877cdd3-636d-498f-9a3a-36e5ed33c497

-- Generated from ChapterMajoranaProp76.lean — solution of BookProof.ChapterMajoranaProp76.energyMomentum_unitary
import Mathlib
import Definitions.Def_ChapterMajoranaProp76
import Theorems.Thm_BookProof_ChapterMajoranaProp76_note4_comp
import Theorems.Thm_BookProof_ChapterMajoranaProp76_energyTransform_unitary
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
theorem solution (Θ : H ≃ₗᵢ[𝕜] K) {V : H → H} {FM : K → K}
    (hV : IsNote4Unitary 𝕜 V) (hFM : IsNote4Unitary 𝕜 FM) :
    IsNote4Unitary 𝕜 (energyTransform Θ V ∘ FM) := note4_comp hFM (energyTransform_unitary Θ hV)
