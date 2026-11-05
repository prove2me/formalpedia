-- Prove2me | solution 1 for Eight.Width.nodup_freshFin
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:26:11.084853+00:00
-- url     : https://prove2.me/submissions/2c76054d-c499-496c-ac4b-942e6ec83b87

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
variable {n : ℕ}

theorem solution (n N : ℕ) : (freshFin n N).Nodup := by
  exact (List.nodup_finRange N).map (Fin.natAdd_injective N n)
