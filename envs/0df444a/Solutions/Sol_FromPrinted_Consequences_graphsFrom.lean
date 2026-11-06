-- Prove2me | solution 1 for FromPrinted.Consequences.graphsFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:26:30.833195+00:00
-- url     : https://prove2.me/submissions/fc6de020-2d7f-40c2-a442-31d06a4bdfbe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_GraphDefs
import Definitions.Def_FromPrinted_Count
import Definitions.Def_FromPrinted_Sets
import Definitions.Def_FromPrinted_Dom
import Definitions.Def_Consequences_Main
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Definitions.Def_Eight_ViaGrouping_CorENP
import Definitions.Def_GraphProblems_Host
import Definitions.Def_GraphProblems_SetTM
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Color
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Circuits
import Theorems.Thm_FromPrinted_Consequences_tm_of_colorings
import Theorems.Thm_ClauseBound_Alg_CertLevel_bits_polyT
import Theorems.Thm_Consequences_tm_of_counts
import Theorems.Thm_GraphProblems_bits_polyT
import Theorems.Thm_GraphProblems_nzW_polyT
import Theorems.Thm_GraphProblems_stDecide
import Theorems.Thm_GraphProblems_stDecideColor


set_option autoImplicit false
section
section
open Consequences
open FromPrinted FromPrinted.Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping FromPrinted.SplitCount Turing
namespace FromPrinted.Consequences
theorem _root_.solution (hSets : StSetsCounted) (hDom : StDominatingCounted) (hCol : StColoringsCounted) : GraphsByCounting := by
  refine ⟨fun δ hδ => ?_, fun δ hδ => ?_⟩
  · obtain ⟨ℓ, τ, c, ⟨p1, h1⟩, ⟨p2, h2⟩, ⟨p3, h3⟩⟩ := hSets (δ / 2) (by positivity)
    obtain ⟨w, ℓ', τ', c', -, p4, h4⟩ := hDom (δ / 2) (by positivity)
    exact ⟨tm_of_counts p1 hδ h1 Nat.bits bits_polyT, tm_of_counts p2 hδ h2 Nat.bits bits_polyT, tm_of_counts p3 hδ h3 Nat.bits bits_polyT,
      tm_of_counts p4 hδ h4 Nat.bits bits_polyT, fun k hk => tm_of_colorings hCol k hk hδ Nat.bits bits_polyT⟩
  · -- «In particular, they decide …»
    obtain ⟨ℓ, τ, c, ⟨p1, h1⟩, ⟨p2, h2⟩, ⟨p3, h3⟩⟩ := hSets (δ / 2) (by positivity)
    obtain ⟨w, ℓ', τ', c', -, p4, h4⟩ := hDom (δ / 2) (by positivity)
    refine ⟨?_, ?_, ?_, ?_, fun k hk => ?_⟩
    · obtain ⟨M, C, hf, h⟩ := tm_of_counts p1 hδ h1 nzW nzW_polyT
      exact ⟨M, C, hf, fun n G s hs => ⟨_, by
        rw [decide_eq_true_iff]
        exact (stDecide n G s hs).1.symm, h n G s hs⟩⟩
    · obtain ⟨M, C, hf, h⟩ := tm_of_counts p2 hδ h2 nzW nzW_polyT
      exact ⟨M, C, hf, fun n G s hs => ⟨_, by
        rw [decide_eq_true_iff]
        exact (stDecide n G s hs).2.1.symm, h n G s hs⟩⟩
    · obtain ⟨M, C, hf, h⟩ := tm_of_counts p3 hδ h3 nzW nzW_polyT
      exact ⟨M, C, hf, fun n G s hs => ⟨_, by
        rw [decide_eq_true_iff]
        exact (stDecide n G s hs).2.2.1.symm, h n G s hs⟩⟩
    · obtain ⟨M, C, hf, h⟩ := tm_of_counts p4 hδ h4 nzW nzW_polyT
      exact ⟨M, C, hf, fun n G s hs => ⟨_, by
        rw [decide_eq_true_iff]
        exact (stDecide n G s hs).2.2.2.symm, h n G s hs⟩⟩
    · obtain ⟨M, C, hf, h⟩ := tm_of_colorings hCol k hk hδ nzW nzW_polyT
      exact ⟨M, C, hf, fun n G => ⟨_, by
        rw [decide_eq_true_iff]
        exact (stDecideColor k n G).symm, h n G⟩⟩
end FromPrinted.Consequences
