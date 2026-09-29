-- Prove2me | solution 1 for FamousTheorems.moore_aronszajn_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:59:24.016916+00:00
-- url     : https://prove2.me/submissions/8872e4f1-2fa2-40aa-8b9a-ef8b48e98350

import Mathlib

universe u v w

theorem solution {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {V : Type w} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [CompleteSpace V] (K : Matrix X X (V →L[𝕜] V)) (hK : K.PosSemidef) :
    ∃ (H : Type (max v w u)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace 𝕜 H) (_ : CompleteSpace H)
      (_ : RKHS 𝕜 H X V), RKHS.kernel H = K :=
  by have : Fact K.PosSemidef := ⟨hK⟩; exact ⟨RKHS.OfKernel K, inferInstance, inferInstance, inferInstance, inferInstance, RKHS.OfKernel.kernel_ofKernel⟩
