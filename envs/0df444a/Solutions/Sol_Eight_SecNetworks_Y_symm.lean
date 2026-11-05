-- Prove2me | solution 1 for Eight.SecNetworks.Y_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:20:45.709375+00:00
-- url     : https://prove2.me/submissions/789dce6c-24a3-408d-a0e1-817638b936b8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Eight_SecNetworks_Grouping
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Finset Groundwork.Colouring
variable {g K : ℕ}
namespace Eight.SecNetworks
theorem _root_.solution {c : Fin g → Fin g → ℕ} (hs : ∀ a b, c a b = c b a) (χ : Fin g → Fin K) (γ γ' : Fin K) : Y c χ γ γ' = Y c χ γ' γ := by
  unfold Y
  rw [sum_comm]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => hs _ _
end Eight.SecNetworks
