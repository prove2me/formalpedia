-- Prove2me | solution 1 for Eight.Width.numFresh_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:43:39.100163+00:00
-- url     : https://prove2.me/submissions/b9129212-c361-4446-a2c3-c064b0704ec3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
import Theorems.Thm_Eight_Width_numFresh_cons

set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
namespace Eight.Width
theorem _root_.solution (k : ℕ) : ∀ φ : List (List (V × Bool)), (∀ C ∈ φ, C.length ≤ k) → numFresh φ ≤ (k - 3) * φ.length
  | [], _ => by simp [numFresh]
  | C :: φ, h => by
    have h1 := h C (by simp)
    have h2 := solution k φ fun D hD => h D (List.mem_cons_of_mem _ hD)
    rw [numFresh_cons, List.length_cons, Nat.mul_succ]
    omega
end Eight.Width
