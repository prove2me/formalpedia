-- Prove2me | solution 1 for Eight.ViaGrouping.is_ofNetwork
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:47:40.045623+00:00
-- url     : https://prove2.me/submissions/8d80a332-234f-43ab-b2fd-490699534b35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Bridge
import Theorems.Thm_P2M_Eight_ViaGrouping___swap_ofPaperNetwork_67bf4c102d66
import Theorems.Thm_Eight_ViaGrouping_n_le_ofPaperNetwork
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Paper_Psi_def
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Finset Stepped Eight.SecNetworks
variable {g : ℕ}
namespace Eight.ViaGrouping
theorem _root_.solution {C : Type} {Np : Paper.NetworkProcedures C} {c : C} {N : Paper.Network (Fin g) (List Bool) (List Bool)} {P B τ S : ℕ}
    (hP : 1 ≤ P) (h : Paper.IsNetwork Np c N P B τ S) : (ofNetwork N fun a => Np.n c a).Is P (B + 1) := by
  have hlt : ∀ x : ℤ, |x| ≤ 2 ^ B → |x| < 2 ^ (B + 1) := fun x hx => by
    have : (0 : ℤ) < 2 ^ B := by positivity
    rw [pow_succ]
    omega
  exact
  { P_pos := hP
    B_pos := by omega
    len_S := fun a z hz => by
      have hz' : z ∈ N.S a := hz
      rw [h.presented.S_eq a] at hz'
      exact mem_words.1 hz'
    len_le := n_le_ofPaperNetwork h
    Ψ_symm := fun a b _ z _ z' _ => Ψ_swap_ofPaperNetwork N a b z z'
    c_symm := h.sized.c_symm
    fact := fun a b hab z _ z' _ => by
      change N.Ψ a b z z' = ∑ θ ∈ words (N.c a b), N.f a b z θ * N.f b a z' θ
      rw [Paper.Psi_def, h.presented.lab_eq a b hab, h.presented.c_eq a b hab]
    i := h.sized.sum_c
    ii_W := fun a z _ => hlt _ (h.sized.abs_W a z)
    ii_Ψ := fun a b hab z _ z' _ => hlt _ (h.sized.abs_Ψ a b z z' hab)
    ii_f := fun a b _ z _ θ _ => hlt _ (h.sized.abs_f a b z θ) }
end Eight.ViaGrouping
