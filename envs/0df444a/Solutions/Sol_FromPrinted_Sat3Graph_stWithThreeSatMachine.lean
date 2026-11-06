-- Prove2me | solution 1 for FromPrinted.Sat3Graph.stWithThreeSatMachine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:16:31.614923+00:00
-- url     : https://prove2.me/submissions/742b185a-a8e7-489e-8c9d-14ac475910f4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_SatDefs
import Definitions.Def_FromPrinted_Core
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_Sat3Graph_Sets
import Definitions.Def_Sat3Graph_Dominating
import Definitions.Def_Sat3Graph_Coloring
import Definitions.Def_Sat3Graph_Cert
import Definitions.Def_Sat3Graph_Host
import Definitions.Def_Sat3Graph_Main
import Definitions.Def_SizeCircuit_Circuit
import Definitions.Def_SizeCircuit_Cert
import Definitions.Def_Complement_Readers
import Definitions.Def_GraphProblems_DomTree
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Sat3Graph
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_key
import Theorems.Thm_FromPrinted_SplitSat_stCore3
import Theorems.Thm_GraphProblems_stShortens
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Sat3Graph_decidesColor_mono
import Theorems.Thm_Sat3Graph_decidesGraph_mono
import Theorems.Thm_Sat3Graph_stCert
import Theorems.Thm_Sat3Graph_stColoring
import Theorems.Thm_Sat3Graph_stDominating
import Theorems.Thm_Sat3Graph_stSets
import Theorems.Thm_SplitSat_stCore3


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper SizeCircuit Complement Sat3Graph
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat
open FromPrinted FromPrinted.Sat3Graph
namespace FromPrinted.Sat3Graph
theorem _root_.solution : StWithThreeSatMachine := by
  intro gates a hT hC δ hδ k hk
  obtain ⟨w, -, hw⟩ := stShortens (δ / 2) (by positivity)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (a : ℝ) + 1 + 3 * ((w - 3 : ℕ) : ℝ) + 2 * (k : ℝ) := ⟨_, rfl⟩
  have hw0 : (0 : ℝ) ≤ ((w - 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hQ0 : 0 < Q := by rw [hQ]; linarith
  obtain ⟨δ₃, hδ₃⟩ : ∃ δ₃ : ℝ, δ₃ = δ / (2 * Q) := ⟨_, rfl⟩
  have h0 : 0 < δ₃ := by rw [hδ₃]; positivity
  have hmul : δ₃ * Q = δ / 2 := by rw [hδ₃, div_mul_eq_mul_div, mul_div_mul_right _ _ hQ0.ne']
  have key : ∀ y : ℝ, y ≤ Q → δ₃ * y ≤ δ / 2 := fun y hy => (mul_le_mul_of_nonneg_left hy h0.le).trans hmul.le
  obtain ⟨ℓ, τ, hP, c, hD⟩ := FromPrinted.SplitSat.stCore3 δ₃ h0
  obtain ⟨c₁, s1, s2, s3⟩ := stSets gates a hT δ δ₃ hδ h0.le ((key _ (by rw [hQ]; linarith)).trans (by linarith)) _ c hD
  obtain ⟨c₂, d1⟩ := stDominating gates a hT w δ δ₃ hδ h0.le hw (key _ (by rw [hQ]; linarith)) _ c hD
  obtain ⟨c₃, k1⟩ := stColoring k hk δ δ₃ hδ h0.le ((key _ (by rw [hQ]; linarith)).trans (by linarith)) _ c hD
  obtain ⟨p1, p2, p3, p4, p5⟩ := stCert gates hC _ hP
  exact ⟨ℓ, τ, w, c₁ + c₂ + c₃, ⟨p1, p2, p3, p4 w, p5 k⟩, decidesGraph_mono le_rfl (by omega) s1, decidesGraph_mono le_rfl (by omega) s2,
    decidesGraph_mono le_rfl (by omega) s3, decidesGraph_mono le_rfl (by omega) d1,
    decidesColor_mono (Ms := COLOR k (core3 ℓ τ)) (k := k) le_rfl (by omega) k1⟩
end FromPrinted.Sat3Graph
