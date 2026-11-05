-- Prove2me | solution 1 for Coding.div_eq_iff_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:59:52.109991+00:00
-- url     : https://prove2.me/submissions/6376d734-bbc1-4362-bc28-caf17ef81214

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Defs
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Coding_OccLists
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count
namespace Coding
theorem _root_.solution {μ e a : ℕ} (hμ : 0 < μ) : e / μ = a ↔ a * μ ≤ e ∧ e < a * μ + μ := by
  constructor
  · rintro rfl
    exact ⟨Nat.div_mul_le_self e μ, Nat.lt_div_mul_add hμ⟩
  · rintro ⟨h1, h2⟩
    exact Nat.div_eq_of_lt_le h1 (by rw [Nat.succ_mul]; exact h2)
end Coding
