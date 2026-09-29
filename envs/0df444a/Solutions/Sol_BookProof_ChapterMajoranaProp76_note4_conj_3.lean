-- Prove2me | solution 3 for BookProof.ChapterMajoranaProp76.note4_conj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T06:02:34.245719+00:00
-- url     : https://prove2.me/submissions/b91b643d-d8b6-469a-8044-39f681914b71

-- Generated from ChapterMajoranaProp76.lean — solution of BookProof.ChapterMajoranaProp76.note4_conj
import Mathlib
import Definitions.Def_ChapterMajoranaProp76
import Theorems.Thm_BookProof_ChapterMajoranaProp76_LinearIsometryEquiv_isNote4Unitary
import Theorems.Thm_BookProof_ChapterMajoranaProp76_note4_comp
open BookProof.ChapterMajoranaProp76











open scoped InnerProductSpace


variable {𝕜 : Type*} [RCLike 𝕜]


variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
  [NormedAddCommGroup L] [InnerProductSpace 𝕜 L]

set_option maxHeartbeats 1000000 in
theorem solution (Θ : H ≃ₗᵢ[𝕜] K) {V : H → H} (hV : IsNote4Unitary 𝕜 V) :
    IsNote4Unitary 𝕜 ((Θ : H → K) ∘ V ∘ (Θ.symm : K → H)) := by

  have hΘ : IsNote4Unitary 𝕜 (Θ : H → K) := LinearIsometryEquiv.isNote4Unitary Θ
  have hΘs : IsNote4Unitary 𝕜 (Θ.symm : K → H) :=
    LinearIsometryEquiv.isNote4Unitary Θ.symm
  have h1 : IsNote4Unitary 𝕜 (V ∘ (Θ.symm : K → H)) := note4_comp hΘs hV
  simpa [Function.comp_assoc] using note4_comp h1 hΘ
