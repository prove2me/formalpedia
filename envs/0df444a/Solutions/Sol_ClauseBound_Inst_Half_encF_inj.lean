-- Prove2me | solution 1 for ClauseBound.Inst.Half.encF_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:24:56.002214+00:00
-- url     : https://prove2.me/submissions/956da28d-dada-4a4b-bf2d-7d4b48073409

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Theorems.Thm_ClauseBound_Inst_Half_ofWord_bitsOf_inj
import Theorems.Thm_ClauseBound_Inst_Half_encF_eq_getElem
import Theorems.Thm_ClauseBound_Inst_Half_nodup_map_coe_allTab_getD
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork ClauseBound.Alg
variable {lam h W : ℕ}
namespace ClauseBound.Inst.Half
theorem _root_.solution (hW : h ≤ W) (hp : 2 ^ lam ≤ Partitions.p h) (x v : Pieces.Bits lam)
    (e : (encF (allTab W) h (bitsOf x) : Multiset ℕ) = encF (allTab W) h (bitsOf v)) : x = v := by
  rw [encF_eq_getElem hW hp x, encF_eq_getElem hW hp v] at e
  have h1 := nodup_map_coe_allTab_getD hW
  have hx := ofWord_bitsOf_lt_length hW hp x
  have hv := ofWord_bitsOf_lt_length hW hp v
  have h2 : (((allTab W).getD h []).map fun L : List ℕ => (L : Multiset ℕ))[ofWord (bitsOf x)]'(by rw [List.length_map]; exact hx)
      = (((allTab W).getD h []).map fun L : List ℕ => (L : Multiset ℕ))[ofWord (bitsOf v)]'(by rw [List.length_map]; exact hv) := by
    rw [List.getElem_map, List.getElem_map]
    exact e
  exact ofWord_bitsOf_inj (h1.getElem_inj_iff.1 h2)
end ClauseBound.Inst.Half
