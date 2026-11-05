-- Prove2me | solution 1 for ClauseBound.Inst.Half.mem_flatten_of_mem_labs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:29:46.718635+00:00
-- url     : https://prove2.me/submissions/6a512c15-cadc-47cb-afa4-f01d9fb4bea0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_ClauseBound_Inst_HalfLabs
import Theorems.Thm_ClauseBound_Inst_Half_Labs_mem_flatten_of_mem_getD
import Theorems.Thm_ClauseBound_Inst_Half_mem_labs

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Part Partitions
open Labs
namespace ClauseBound.Inst.Half
theorem _root_.solution {T : PT} {tr : Bool} {h : ℕ} {s : ℤ} {p : ℕ × List ℕ} (hp : p ∈ labs T tr h s) : p.2 ∈ T.flatten ∧ p.1 ≤ 2 * h :=
  ⟨mem_flatten_of_mem_getD (mem_labs.1 hp).2.2, (mem_labs.1 hp).1⟩
end ClauseBound.Inst.Half
