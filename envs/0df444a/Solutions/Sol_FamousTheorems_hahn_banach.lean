-- Prove2me | solution 1 for FamousTheorems.hahn_banach
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T17:48:50.876921+00:00
-- url     : https://prove2.me/submissions/494b2bd0-59d1-40f0-bc7f-06c1de4805d2

import Mathlib

theorem solution {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] (p : Subspace 𝕜 E) (f : StrongDual 𝕜 p) :
    ∃ g : StrongDual 𝕜 E, (∀ x : p, g x = f x) ∧ ‖g‖ = ‖f‖ :=
  exists_extension_norm_eq p f
