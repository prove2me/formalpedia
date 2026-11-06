-- Prove2me | solution 1 for Complement.stCliques
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:16:36.637745+00:00
-- url     : https://prove2.me/submissions/48f2f40e-06f0-4bd7-993c-9b81136e7c25

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Complement_Defs
import Definitions.Def_GraphProblems_Read
import Mathlib.Tactic
import Definitions.Def_Complement_Sets
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open Complement
open Groundwork Groundwork.Prog CountKSat GraphProblems
namespace Complement
theorem _root_.solution : StCliques := fun n G s => by
  have h : ∀ S : Finset (Fin n), G.IsNClique s S ↔ Gᶜ.IsNIndepSet s S := fun S => by rw [SimpleGraph.isNIndepSet_compl]
  refine ⟨h, ?_⟩
  unfold numCliques numIndepSets
  congr 1
  ext S
  exact h S
end Complement
