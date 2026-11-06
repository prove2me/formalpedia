-- Prove2me | solution 1 for FromPrinted.Consequences.SIZED_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:05:33.142206+00:00
-- url     : https://prove2.me/submissions/a606fda1-70b2-45ab-b40b-e9e85c07636a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_GraphDefs
import Definitions.Def_FromPrinted_Count
import Definitions.Def_Consequences_Sets
import Definitions.Def_SizeCircuit_Main
import Definitions.Def_Complement_Readers
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_SetTM
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Sets
import Theorems.Thm_FromPrinted_SplitCount_stEngineCounts
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_SizeCircuit_stSizeGates
import Theorems.Thm_SizeCircuit_stSizedFromEngines
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Consequences
open FromPrinted FromPrinted.Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping FromPrinted.SplitCount SizeCircuit Complement
namespace FromPrinted.Consequences
theorem _root_.solution (w : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ ℓ τ : ℕ, PolyTimeSteps (SIZED w ℓ τ) ∧ ∃ c : ℕ, ∀ (n s : ℕ) (ψ : Fml), s ≤ n → Shaped w n ψ →
    ∃ T : ℕ, (SIZED w ℓ τ).Runs (List.replicate n (), s, ψ) T (c * (n + ψ.length + 2) ^ c) (cntS n s ψ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n) := by
  obtain ⟨a, hT, hC⟩ := stSizeGates
  exact stSizedFromEngines ENGINEsplit stEngineCounts sizeGates a hT hC w δ hδ
end FromPrinted.Consequences
