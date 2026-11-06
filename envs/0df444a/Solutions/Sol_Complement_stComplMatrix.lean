-- Prove2me | solution 1 for Complement.stComplMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:18:42.436027+00:00
-- url     : https://prove2.me/submissions/d4a0131a-3232-495b-9397-37234abfdd97

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Complement_Defs
import Definitions.Def_GraphProblems_Read
import Mathlib.Tactic
import Definitions.Def_Complement_Sets
import Theorems.Thm_Complement_pairs_eq
import Theorems.Thm_Complement_entry_compl

set_option autoImplicit false
section
section
open Complement
open Groundwork Groundwork.Prog CountKSat GraphProblems
namespace Complement
theorem _root_.solution : StComplMatrix := fun n G => by
  obtain ⟨m, hm⟩ : ∃ m, m = matrix G := ⟨_, rfl⟩
  rw [← hm, complMatrix, pairs_eq, matrix, List.map_flatMap]
  refine List.flatMap_congr fun u _ => ?_
  rw [List.map_map]
  refine List.map_congr_left fun v _ => ?_
  rw [hm]
  exact entry_compl G u v _
end Complement
