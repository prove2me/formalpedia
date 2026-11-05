-- Prove2me | solution 1 for CountKSat.cntN_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:31:48.571069+00:00
-- url     : https://prove2.me/submissions/0c3fe7f1-bea1-435f-aa66-dd924c732906

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_Refine
import Mathlib.Tactic.Tauto
import Definitions.Def_CountKSat_StepCount
import Theorems.Thm_CountKSat_StepCount_pickK_petals
import Theorems.Thm_CountKSat_cntN_split
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog
open StepCount
namespace CountKSat
theorem _root_.solution {θ : ℕ → ℕ} {k : ℕ} (n : ℕ) {x l h : CNode} (hst : stepC θ k x = some (l, h)) :
    cntN n (leafF x) = cntN n (leafF l) + cntN n (leafF h) := by
  obtain ⟨⟨H, P⟩, hp, he⟩ := Option.map_eq_some_iff.1 hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact cntN_split n x.2 x.1 H P (pickK_petals hp)
end CountKSat
