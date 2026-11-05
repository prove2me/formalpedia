-- Prove2me | solution 1 for ClauseBound.ParityChecks.Shape.occ_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:50:15.363295+00:00
-- url     : https://prove2.me/submissions/11970229-e191-4403-b2a4-e5d98e7ae0b7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks
namespace ClauseBound.ParityChecks.Shape
theorem _root_.solution (x : Fml) (v : ℕ) : occ x v = x.filter (hasV v) := rfl
end ClauseBound.ParityChecks.Shape
