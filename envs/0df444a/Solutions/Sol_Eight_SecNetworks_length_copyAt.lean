-- Prove2me | solution 1 for Eight.SecNetworks.length_copyAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:09:51.445688+00:00
-- url     : https://prove2.me/submissions/fd7693d2-0fc3-4366-bdb5-7c4ad592c878

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_StepMachines_Prog_NetVal
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_Clique
import Theorems.Thm_Eight_SecNetworks_place_lt
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_length_block
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Groundwork Groundwork.Prog Finset
namespace Eight.SecNetworks
theorem _root_.solution {K lam : ℕ} (w w' : Fin K) (h : w' ≠ w) {z : List Bool} (hz : z.length = (K - 1) * lam) :
    (copyAt lam w w' z).length = lam := by
  refine length_block ?_
  rw [hz]
  exact Nat.mul_le_mul_right _ (place_lt w w' h)
end Eight.SecNetworks
