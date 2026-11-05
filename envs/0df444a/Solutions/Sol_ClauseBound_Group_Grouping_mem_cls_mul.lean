-- Prove2me | solution 1 for ClauseBound.Group.Grouping.mem_cls_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:58:32.249198+00:00
-- url     : https://prove2.me/submissions/aa5e254a-6ef4-4433-a8c2-a997be088f6f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Group_Sample
import Definitions.Def_ClauseBound_Group_Grouping
import Theorems.Thm_ClauseBound_Group_Grouping_mem_cls

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Group
open Finset
open ClauseBound.Group.Grouping
variable {K n : ℕ}
namespace ClauseBound.Group.Grouping
theorem _root_.solution {e p : Equiv.Perm (Fin (K * n))} {γ : Fin K} {a : Fin (K * n)} : a ∈ cls (e * p) γ ↔ p a ∈ cls e γ := by
  rw [mem_cls, mem_cls, Equiv.Perm.mul_apply]
end ClauseBound.Group.Grouping
