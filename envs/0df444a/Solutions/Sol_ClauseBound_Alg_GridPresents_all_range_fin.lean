-- Prove2me | solution 1 for ClauseBound.Alg.GridPresents.all_range_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:16:10.647219+00:00
-- url     : https://prove2.me/submissions/87ea38d2-d946-49f3-8d69-1ced3b56a1e7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet
namespace ClauseBound.Alg.GridPresents
theorem _root_.solution (n : ℕ) (t : ℕ → Bool) : (List.range n).all t = true ↔ ∀ i : Fin n, t i = true := by
  rw [List.all_eq_true]
  exact ⟨fun h i => h i (List.mem_range.2 i.2), fun h i hi => h ⟨i, List.mem_range.1 hi⟩⟩
end ClauseBound.Alg.GridPresents
