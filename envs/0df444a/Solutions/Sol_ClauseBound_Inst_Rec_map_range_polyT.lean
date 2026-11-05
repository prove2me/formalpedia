-- Prove2me | solution 1 for ClauseBound.Inst.Rec.map_range_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:07:15.72606+00:00
-- url     : https://prove2.me/submissions/c8383a40-bc88-41aa-bc0e-ae08f3b2e631

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Data
import Definitions.Def_ClauseBound_Rec_Defs
import Definitions.Def_ClauseBound_Rec_CountRow
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_RecArith
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Rec
open Finset Polynomial Groundwork PaddedDescent.F ClauseBound.Rec
variable {α β : Type} [Enc α] [Enc β]
namespace ClauseBound.Inst.Rec
theorem _root_.solution {w : α → ℕ} {f : α → ℕ → β} (hw : Unary w) (hf : PolyT fun p : α × ℕ => f p.1 (min p.2 (w p.1))) :
    PolyT fun x => (List.range (w x)).map (f x) := by
  have h : PolyT fun x => (List.range (w x)).map fun k => f x (min k (w x)) :=
    PolyT.map (f := fun x k => f x (min k (w x))) hf (range_polyT hw)
  exact h.congr fun x => List.map_congr_left fun k hk => by rw [min_eq_left (List.mem_range.1 hk).le]
end ClauseBound.Inst.Rec
