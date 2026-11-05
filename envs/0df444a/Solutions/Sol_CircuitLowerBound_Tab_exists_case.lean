-- Prove2me | solution 1 for CircuitLowerBound.Tab.exists_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:42:54.32477+00:00
-- url     : https://prove2.me/submissions/991672c6-fd4b-4e26-b74b-ce888b3f6dc9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Sound

set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool)
variable {N} [Finite (Case N)] {α : Atom N → ℕ → ℕ → Bool} {b Q P : ℕ}
namespace CircuitLowerBound.Tab
theorem _root_.solution (h : Spec N α b Q P) {t : ℕ} (ht : t < 2 ^ b) : ∃ γ, α (.cs γ) t 0 = true := by
  have key : ∀ (i : ℕ) (hi : i < nc N + 1), α (.pre ⟨i, hi⟩) t 0 = true → ∃ γ, α (.cs γ) t 0 = true := by
    intro i
    induction i with
    | zero =>
      intro hi h0
      have := h.preBot t ht
      rw [show (0 : Fin (nc N + 1)) = ⟨0, hi⟩ from rfl, h0] at this
      cases this
    | succ i ih =>
      intro hi h1
      rcases h.preStep t ht ⟨i, by omega⟩ with h2 | h2 | h2
      · rw [show (Fin.succ ⟨i, by omega⟩ : Fin (nc N + 1)) = ⟨i + 1, hi⟩ from rfl, h1] at h2
        cases h2
      · exact ih _ h2
      · exact ⟨_, h2⟩
  exact key _ _ (h.preTop t ht)
end CircuitLowerBound.Tab
