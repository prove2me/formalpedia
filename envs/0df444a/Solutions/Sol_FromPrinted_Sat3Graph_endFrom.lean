-- Prove2me | solution 1 for FromPrinted.Sat3Graph.endFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:15:51.419641+00:00
-- url     : https://prove2.me/submissions/be2aafe3-227a-4451-ade7-25957a82f63b

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
import Theorems.Thm_Sat3Graph_decidesInTime_of_hosted


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper SizeCircuit Complement Sat3Graph
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat
open FromPrinted FromPrinted.Sat3Graph
namespace FromPrinted.Sat3Graph
theorem _root_.solution : StTiedTM → ThreeSatStatement := by
  intro hTied δ hδ
  obtain ⟨gates, a, ℓ, τ, w, c, -, -, ⟨-, -, h1⟩, ⟨-, -, h2⟩, ⟨-, -, h3⟩, ⟨-, -, h4⟩, -⟩ := hTied δ hδ 3 le_rfl
  refine ⟨decidesInTime_of_hosted h1, decidesInTime_of_hosted h2, decidesInTime_of_hosted h3, decidesInTime_of_hosted h4, fun k hk => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, M, C, q, hf, -, hM⟩ := hTied δ hδ k hk
  exact ⟨M, C, hf, hM⟩
end FromPrinted.Sat3Graph
