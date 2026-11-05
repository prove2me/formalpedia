-- Prove2me | solution 1 for ClauseBound.Group.Grouping.mem_cls
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:42:23.32366+00:00
-- url     : https://prove2.me/submissions/ac8bc7d5-3cdf-455c-ba78-6dc6ca7f71b8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Group_Sample
import Definitions.Def_ClauseBound_Group_Grouping

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Group
open Finset
open ClauseBound.Group.Grouping
variable {K n : ℕ}
namespace ClauseBound.Group.Grouping
theorem _root_.solution {e : Equiv.Perm (Fin (K * n))} {γ : Fin K} {a : Fin (K * n)} : a ∈ cls e γ ↔ chi0 (e a) = γ := by simp [cls]
end ClauseBound.Group.Grouping
