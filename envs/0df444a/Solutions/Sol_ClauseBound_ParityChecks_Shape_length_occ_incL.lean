-- Prove2me | solution 1 for ClauseBound.ParityChecks.Shape.length_occ_incL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:18:07.483858+00:00
-- url     : https://prove2.me/submissions/be188048-5883-49bf-b4f6-0bea50ffbc91

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_ClauseBound_ParityChecks_Shape_occ_eq
import Theorems.Thm_ClauseBound_ParityChecks_Shape_length_filter_flatMap_range
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks
variable {k n Δ : ℕ} {q : Par} {ψ : Fml} {Lam : List Chk} {j : ℕ}
namespace ClauseBound.ParityChecks.Shape
theorem _root_.solution (n : ℕ) (ψ : Fml) (Lam : List Chk) (j v : ℕ) : (occ (incL n ψ Lam j) v).length =
    ∑ j' ∈ range j, (Lam.getD j' []).countP (fun x => hasV v (ψ.getD x [] ++ [(n + j', false)])) +
      (Lam.getD j []).countP fun x => hasV v (ψ.getD x []) := by
  rw [occ_eq, incL, List.filter_append, List.length_append, length_filter_flatMap_range]
  congr 1
  · refine Finset.sum_congr rfl fun j' _ => ?_
    rw [List.filter_map, List.length_map, List.countP_eq_length_filter]
    rfl
  · rw [List.filter_map, List.length_map, List.countP_eq_length_filter]
    rfl
end ClauseBound.ParityChecks.Shape
