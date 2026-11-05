-- Prove2me | solution 1 for ClauseBound.Inst.Half.flatOK_allTab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:14:50.411938+00:00
-- url     : https://prove2.me/submissions/9c8ff173-16e1-4dee-9172-58aae72bb805

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Theorems.Thm_ClauseBound_Inst_Half_mem_flatten_allTab


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork ClauseBound.Alg
variable {lam h W : ℕ}
namespace ClauseBound.Inst.Half
theorem _root_.solution (W : ℕ) : FlatOK W (allTab W).flatten where
  inj π hπ σ hσ e :=
    (Multiset.coe_eq_coe.1 e).eq_of_pairwise' (mem_flatten_allTab.1 hπ).2.2 (mem_flatten_allTab.1 hσ).2.2
  erase π hπ l hl := by
    obtain ⟨h1, h2, h3⟩ := mem_flatten_allTab.1 hπ
    refine mem_flatten_allTab.2 ⟨?_, fun n hn => h2 n (List.mem_of_mem_erase hn), h3.sublist List.erase_sublist⟩
    have := List.sum_erase hl
    omega
  sum_le π hπ := (mem_flatten_allTab.1 hπ).1
end ClauseBound.Inst.Half
