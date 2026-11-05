-- Prove2me | solution 1 for CountKSatRate.Tree.sideT_taut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:51:40.256176+00:00
-- url     : https://prove2.me/submissions/183baec0-a68a-4e63-b5ab-1c8d908dc505

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Tactic.Ring
import Definitions.Def_CountKSatRate_Tree
import Theorems.Thm_CountKSat_ProgC_length_taut
import Theorems.Thm_CountKSat_ProgC_sideOK_taut
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open CountKSatRate
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat WidthK.Prog
open WidthK (theta bsum leafC Iface Refines)
open CountKSatRate.Tree
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}
namespace CountKSatRate.Tree
theorem _root_.solution (n k q : ℕ) : SideT n k q (taut n) 0 :=
  ⟨by rw [ProgC.length_taut]; omega, (ProgC.sideOK_taut n k).2.1, fun _ hC => hC, fun _ hC => Or.inl hC⟩
end CountKSatRate.Tree
