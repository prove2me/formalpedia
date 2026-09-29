-- Prove2me | solution 1 for BookProof.ChapterMajoranaProp76.note4_comp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:14:53.520798+00:00
-- url     : https://prove2.me/submissions/5b6b4c0e-095b-4818-87b3-8c5cc4031391

-- Generated from ChapterMajoranaProp76.lean — solution of BookProof.ChapterMajoranaProp76.note4_comp
import Mathlib
import Definitions.Def_ChapterMajoranaProp76
open BookProof.ChapterMajoranaProp76











open scoped InnerProductSpace


variable {𝕜 : Type*} [RCLike 𝕜]


variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
  [NormedAddCommGroup L] [InnerProductSpace 𝕜 L]

set_option maxHeartbeats 1000000 in
theorem solution {f : H → K} {g : K → L}
    (hf : IsNote4Unitary 𝕜 f) (hg : IsNote4Unitary 𝕜 g) :
    IsNote4Unitary 𝕜 (g ∘ f) :=
  ⟨hg.1.comp hf.1, fun x => by
      simp only [Function.comp_apply]
      rw [hg.2 (f x), hf.2 x]⟩
