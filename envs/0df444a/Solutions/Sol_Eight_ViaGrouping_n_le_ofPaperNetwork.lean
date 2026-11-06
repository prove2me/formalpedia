-- Prove2me | solution 1 for Eight.ViaGrouping.n_le_ofPaperNetwork
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:38:46.979165+00:00
-- url     : https://prove2.me/submissions/08cd3deb-5d83-40f1-ae20-b518c0df7b7f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Bridge
import Theorems.Thm_Groundwork_card_words


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Finset Stepped Eight.SecNetworks
variable {g : ℕ}
namespace Eight.ViaGrouping
theorem _root_.solution {C : Type} {Np : Paper.NetworkProcedures C} {c : C} {N : Paper.Network (Fin g) (List Bool) (List Bool)} {P B τ S : ℕ}
    (h : Paper.IsNetwork Np c N P B τ S) (a : Fin g) : Np.n c a ≤ P := by
  have h1 := h.sized.card_S a
  rw [h.presented.S_eq a, card_words] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
end Eight.ViaGrouping
