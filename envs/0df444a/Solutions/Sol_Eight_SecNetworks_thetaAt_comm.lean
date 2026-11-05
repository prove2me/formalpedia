-- Prove2me | solution 1 for Eight.SecNetworks.thetaAt_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:54:08.230259+00:00
-- url     : https://prove2.me/submissions/ecabf605-13ec-44f0-a305-114949ab55e3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_LemGrouping
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_Tables
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Paper
variable {C : Type} {g K : ℕ}
namespace Eight.SecNetworks
theorem _root_.solution (Np : NetworkProcedures C) (c : C) (hK0 : 0 < K) (x : ℕ) (Θ Θ' : Fin K → List Bool) {a b : Fin g} (hne : grouping hK0 x a ≠ grouping hK0 x b)
    (h : Θ (grouping hK0 x b) = Θ' (grouping hK0 x a)) : thetaAt Np c hK0 x Θ a b = thetaAt Np c hK0 x Θ' b a := by
  unfold thetaAt
  rw [h, min_comm, max_comm]
  rcases lt_or_gt_of_ne hne with h1 | h1
  · rw [if_pos h1, if_neg h1.not_gt]
  · rw [if_neg h1.not_gt, if_pos h1]
end Eight.SecNetworks
