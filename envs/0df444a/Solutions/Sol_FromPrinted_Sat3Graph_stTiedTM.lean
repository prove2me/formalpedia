-- Prove2me | solution 1 for FromPrinted.Sat3Graph.stTiedTM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:22:53.950408+00:00
-- url     : https://prove2.me/submissions/694daf91-f630-4179-9cb1-8e96ab232439

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
import Theorems.Thm_FromPrinted_Sat3Graph_stWithThreeSatMachine
import Theorems.Thm_Sat3Graph_decidesColor_mono
import Theorems.Thm_Sat3Graph_decidesGraph_mono
import Theorems.Thm_Sat3Graph_hostedColor_of
import Theorems.Thm_Sat3Graph_hostedFor_of
import Theorems.Thm_SizeCircuit_certGates_sizeGates
import Theorems.Thm_SizeCircuit_testsSize_sizeGates


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper SizeCircuit Complement Sat3Graph
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat
open FromPrinted FromPrinted.Sat3Graph
namespace FromPrinted.Sat3Graph
theorem _root_.solution : StTiedTM := by
  intro δ hδ k hk
  have h2 : δ / 2 ≤ δ := by linarith
  obtain ⟨ℓ, τ, w, c, ⟨p1, p2, p3, p4, p5⟩, s1, s2, s3, d1, k1⟩ :=
    stWithThreeSatMachine sizeGates 6 testsSize_sizeGates certGates_sizeGates (δ / 2) (by positivity) k hk
  exact ⟨sizeGates, 6, ℓ, τ, w, c, testsSize_sizeGates, certGates_sizeGates,
    ⟨p1, decidesGraph_mono h2 le_rfl s1, hostedFor_of hδ p1 s1⟩, ⟨p2, decidesGraph_mono h2 le_rfl s2, hostedFor_of hδ p2 s2⟩,
    ⟨p3, decidesGraph_mono h2 le_rfl s3, hostedFor_of hδ p3 s3⟩, ⟨p4, decidesGraph_mono h2 le_rfl d1, hostedFor_of hδ p4 d1⟩,
    ⟨p5, decidesColor_mono (Ms := COLOR k (core3 ℓ τ)) (k := k) h2 le_rfl k1, hostedColor_of (k := k) hδ p5 k1⟩⟩
end FromPrinted.Sat3Graph
