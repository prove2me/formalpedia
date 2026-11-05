-- Prove2me | solution 1 for ClauseBound.Inst.Half.CertSmall.sOf_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:45:07.612949+00:00
-- url     : https://prove2.me/submissions/0b5ea1f9-ffa8-4f90-8d4f-ade6bcbf6108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.mul



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.CertSmall
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half.CertSmall
theorem _root_.solution {h i : α → ℕ} (hh : PolyT h) (hi : PolyT i) : PolyT fun x => sOf (h x) (i x) := by
  unfold sOf
  exact PolyT.subZ (PolyT.natCast (PolyT.min' hi (PolyT.mul (PolyT.const 4) hh))) (PolyT.mulZ (PolyT.const 2) (PolyT.natCast hh))
end ClauseBound.Inst.Half.CertSmall
