-- Prove2me | solution 1 for ClauseBound.Boson.aFam_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:46:05.003305+00:00
-- url     : https://prove2.me/submissions/557d142c-93bd-4c43-bcaf-53d4e2725295

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Dual

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
namespace ClauseBound.Boson
theorem _root_.solution {μ : List ℕ} (hμ : Pos μ) : (aFam μ).Ok μ.sum := by
  induction μ with
  | nil =>
    intro c hc
    rw [aFam, List.mem_singleton] at hc
    subst hc
    exact ⟨fun n hn => absurd hn List.not_mem_nil, le_rfl⟩
  | cons n μ ih =>
    intro c hc
    rw [aFam, List.mem_flatMap] at hc
    obtain ⟨cj, hcj, hc⟩ := hc
    obtain ⟨cL, hcL, rfl⟩ := List.mem_map.1 hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hcj
    have hi' := List.mem_range.1 hi
    obtain ⟨h1, h2⟩ := ih (fun k hk => hμ k (List.mem_cons_of_mem _ hk)) cL hcL
    refine ⟨fun k hk => ?_, ?_⟩
    · rcases List.mem_cons.1 hk with rfl | hk
      · exact Nat.succ_pos i
      · exact h1 k hk
    · simp only [List.sum_cons]
      omega
end ClauseBound.Boson
