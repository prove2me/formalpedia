-- Prove2me | solution 1 for ClauseBound.Inst.Half.Spec.abs_sOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:18:33.926052+00:00
-- url     : https://prove2.me/submissions/dbc0762b-ce1f-4511-9da3-7a8f46f71b7a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfSpec

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec Finset
open ClauseBound.Inst.Half.Spec
namespace ClauseBound.Inst.Half.Spec
theorem _root_.solution (h i : ℕ) : |sOf h i| ≤ 2 * (h : ℤ) := by
  rw [sOf, abs_le]
  omega
end ClauseBound.Inst.Half.Spec
