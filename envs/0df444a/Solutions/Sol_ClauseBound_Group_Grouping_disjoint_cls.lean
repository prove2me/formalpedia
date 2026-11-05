-- Prove2me | solution 1 for ClauseBound.Group.Grouping.disjoint_cls
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:58:31.156607+00:00
-- url     : https://prove2.me/submissions/db730aff-cce9-4e4e-b8ef-7433509a0b25

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
theorem _root_.solution (e : Equiv.Perm (Fin (K * n))) {γ γ' : Fin K} (h : γ ≠ γ') : Disjoint (cls e γ) (cls e γ') :=
  disjoint_left.2 fun _ h1 h2 => h ((mem_cls.1 h1).symm.trans (mem_cls.1 h2))
end ClauseBound.Group.Grouping
