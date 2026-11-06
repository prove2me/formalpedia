-- Prove2me | solution 1 for Eight.ViaGrouping.ALGO_runs_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:50:28.665908+00:00
-- url     : https://prove2.me/submissions/9277e2f9-e3f5-4561-b828-bfa0da520895

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_ENP
import Definitions.Def_Eight_ViaGrouping_CorDefs2
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_CorENP
import Theorems.Thm_CircuitLowerBound_Alg_runs_algo
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open ENP Groundwork Turing CircuitLowerBound
namespace Eight.ViaGrouping
theorem _root_.solution {En : ℕ → ℕ → ℕ → Paper.StepMachine (List Unit × Groundwork.Prog.Fml) (List Bool)} (h : EngineCounts En) {δ : ℝ} (hδ : 0 < δ) : ∃ ℓ τ c : ℕ, Paper.PolyTimeSteps (En 3 ℓ τ) ∧
    ∀ (a₀ : ℕ) (g : MCode → ℕ) (F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf) (fb : List Unit → Bool), Alg.FormOK a₀ g F → ∀ x : List Bool,
      ∃ (T : ℕ) (b : Bool), (Alg.algo (En 3 ℓ τ) F fb).Runs x T (c * ((Alg.pre F fb x).1.length + 2) ^ c) b ∧ (b = true ↔ ¬Sat (Alg.pre F fb x).2) ∧
        (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * (Alg.pre F fb x).1.length) := by
  obtain ⟨ℓ, τ, hp, c, hc⟩ := h 3 (by norm_num) δ hδ
  exact ⟨ℓ, τ, c, hp, fun a₀ g F fb hF x => Alg.runs_algo (fb := fb) (show Alg.EngineOK (En 3 ℓ τ) c δ from hc) hF x⟩
end Eight.ViaGrouping
