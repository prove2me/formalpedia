-- Prove2me | solution 1 for Eight.SecNetworks.Net.c_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:21:48.839296+00:00
-- url     : https://prove2.me/submissions/a20d9662-49cf-4b48-a4e1-fc5162ac0726

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
import Definitions.Def_ToTuring_Poly_Comb
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_LemGrouping
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Groundwork Groundwork.Prog Finset Stepped
open Eight.SecNetworks.Net
variable {g : ℕ} (N : Net g)
variable {N} {P B : ℕ}
namespace Eight.SecNetworks.Net
theorem _root_.solution (h : N.Is P B) {a b : Fin g} (hab : a ≠ b) : N.c a b ≤ P :=
  (Finset.single_le_sum (f := fun b => N.c a b) (fun _ _ => Nat.zero_le _) (Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩)).trans (h.i a)
end Eight.SecNetworks.Net
