-- Prove2me | solution 1 for DirectFidelity.RandomState.eq_33
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T06:43:48.119843+00:00
-- url     : https://prove2.me/submissions/4e098c1d-3f8b-4e40-8b64-ee96ce24a620

import Mathlib
import Definitions.Def_DirectFidelity_RandomState_Setting

set_option autoImplicit false
open DirectFidelity.RandomState

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Mathematical source: Flammia and Liu, arXiv:1104.4695v3, equation (33).
theorem solution {n : ℕ} (φ : E n) (hφ : ‖φ‖ = 1) :
    ∀ ψ ψ' : E n, ‖inner ℂ φ ψ - inner ℂ φ ψ'‖ ≤ ‖ψ - ψ'‖ := by
  intro ψ ψ'
  rw [← inner_sub_right]
  simpa only [hφ, one_mul] using norm_inner_le_norm (𝕜 := ℂ) φ (ψ - ψ')
