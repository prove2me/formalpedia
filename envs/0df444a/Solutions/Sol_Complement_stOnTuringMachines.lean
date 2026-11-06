-- Prove2me | solution 1 for Complement.stOnTuringMachines
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:14:08.41108+00:00
-- url     : https://prove2.me/submissions/7c9b68ab-4ba5-4d53-ac45-860a6653ecbf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Complement_Defs
import Definitions.Def_Complement_Readers
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Host
import Definitions.Def_ToTuring_Poly_Basic
import Mathlib.Tactic
import Definitions.Def_Complement_Main
import Theorems.Thm_Complement_tm_of_reader
import Theorems.Thm_Complement_stFromSized
import Theorems.Thm_GraphProblems_bits_polyT
import Theorems.Thm_GraphProblems_nzW_polyT
import Theorems.Thm_GraphProblems_stDecide


set_option autoImplicit false
section
section
open Complement
open Groundwork Groundwork.Prog CountKSat GraphProblems Turing
namespace Complement
theorem _root_.solution : StOnTuringMachines := fun hS δ hδ => by
  obtain ⟨Z, hp1, hp2, c, h⟩ := stFromSized hS (δ / 2) (by positivity)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact tm_of_reader _ hp1 (fun _ G s => numCliques G s) hδ c (fun n G s hs => (h n G s hs).1) Nat.bits bits_polyT
  · exact tm_of_reader _ hp2 (fun _ G s => numVertexCovers G s) hδ c (fun n G s hs => (h n G s hs).2) Nat.bits bits_polyT
  · obtain ⟨M, C, hf, hM⟩ := tm_of_reader _ hp1 (fun _ G s => numCliques G s) hδ c (fun n G s hs => (h n G s hs).1) nzW nzW_polyT
    exact ⟨M, C, hf, fun n G s hs => ⟨_, by
      rw [decide_eq_true_iff]
      exact (stDecide n G s hs).2.1.symm, hM n G s hs⟩⟩
  · obtain ⟨M, C, hf, hM⟩ := tm_of_reader _ hp2 (fun _ G s => numVertexCovers G s) hδ c (fun n G s hs => (h n G s hs).2) nzW nzW_polyT
    exact ⟨M, C, hf, fun n G s hs => ⟨_, by
      rw [decide_eq_true_iff]
      exact (stDecide n G s hs).2.2.1.symm, hM n G s hs⟩⟩
end Complement
