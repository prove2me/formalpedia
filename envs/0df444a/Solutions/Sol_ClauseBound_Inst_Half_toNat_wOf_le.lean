-- Prove2me | solution 1 for ClauseBound.Inst.Half.toNat_wOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:28:56.799185+00:00
-- url     : https://prove2.me/submissions/c163d082-0404-4311-b333-dc1cdbc5885b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_ClauseBound_Inst_HalfLabs
import Theorems.Thm_ClauseBound_Inst_Half_wOf_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Part Partitions
open Labs
namespace ClauseBound.Inst.Half
theorem _root_.solution {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * h) (tr : Bool) {j : ℕ} (hj : j ≤ 2 * h) : (wOf tr h s j).toNat ≤ 4 * h := by
  have := wOf_le hs tr hj
  omega
end ClauseBound.Inst.Half
