-- Prove2me | solution 1 for CircuitLowerBound.Alg.runs_algo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:22:20.064969+00:00
-- url     : https://prove2.me/submissions/9769e184-ff45-401d-9fe4-5fc4777cb905

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Alg_Parse
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_PaddedDescent_Host
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Machine
import Theorems.Thm_CircuitLowerBound_Alg_shaped_pre
import Theorems.Thm_CircuitLowerBound_Alg_cntN_eq_zero_iff
import Theorems.Thm_CircuitLowerBound_Alg_cntN_lt
import Theorems.Thm_CircuitLowerBound_Alg_isZ_binary
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_Stepped_mapOut_runs
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing Parse
open CircuitLowerBound.Alg
variable {F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf} {fb : List Unit → Bool}
variable {a₀ : ℕ} {g : MCode → ℕ}
namespace CircuitLowerBound.Alg
theorem _root_.solution {E : Stepped (List Unit × Prog.Fml) (List Bool)} {c : ℕ} {δ : ℝ} (hE : EngineOK E c δ) (hF : FormOK a₀ g F) (x : List Bool) :
    ∃ (T : ℕ) (b : Bool), (algo E F fb).Runs x T (c * ((pre F fb x).1.length + 2) ^ c) b ∧ (b = true ↔ ¬Sat (pre F fb x).2) ∧
      (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * (pre F fb x).1.length) := by
  obtain ⟨h1, h2⟩ := shaped_pre (fb := fb) hF x
  obtain ⟨T, hr, hT⟩ := hE _ _ h1 h2
  have e : (List.replicate (pre F fb x).1.length (), (pre F fb x).2) = pre F fb x :=
    Prod.ext (List.eq_replicate_iff.2 ⟨rfl, fun _ _ => rfl⟩).symm rfl
  rw [e] at hr
  exact ⟨T, _, Stepped.mapOut_runs (Stepped.mapIn_runs hr),
    (isZ_binary (cntN_lt _ _)).trans (cntN_eq_zero_iff fun D hD => (h1 D hD).2), hT⟩
end CircuitLowerBound.Alg
