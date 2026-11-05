-- Prove2me | solution 1 for Eight.SecNetworks.place_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:07:34.804733+00:00
-- url     : https://prove2.me/submissions/a099b76a-3ba1-4886-91e3-f5b215e6646c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_StepMachines_Prog_NetVal
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_Clique

set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Groundwork Groundwork.Prog Finset
namespace Eight.SecNetworks
theorem _root_.solution {K : ℕ} (w w' : Fin K) (h : w' ≠ w) : place w w' < K - 1 := by
  have := Fin.val_ne_of_ne h
  unfold place
  split_ifs <;> omega
end Eight.SecNetworks
