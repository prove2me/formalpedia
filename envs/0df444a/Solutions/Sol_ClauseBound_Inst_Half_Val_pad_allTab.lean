-- Prove2me | solution 1 for ClauseBound.Inst.Half.Val.pad_allTab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:22:42.914301+00:00
-- url     : https://prove2.me/submissions/627fdf12-82c7-4e31-8aab-edfa22d50d8f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfVal
import Theorems.Thm_ClauseBound_Inst_Half_Val_deltaF_eq
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec Finset
open ClauseBound.Inst.Half.Val
namespace ClauseBound.Inst.Half.Val
theorem _root_.solution {h : ℕ} {pad : U} (hp : padLen h ≤ pad.length) :
    (7 * (4 * h) + 10) * ∑ E ∈ range (4 * h + 1), Partitions.p E ≤ pad.length := by
  refine le_trans ?_ hp
  rw [← deltaF_eq, padLen]
  have h1 : h + 2 ≤ (h + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
  have h2 : deltaF h + 1 ≤ (deltaF h + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  exact Nat.mul_le_mul (by omega) (by omega)
end ClauseBound.Inst.Half.Val
