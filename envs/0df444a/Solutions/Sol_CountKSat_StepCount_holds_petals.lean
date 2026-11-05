-- Prove2me | solution 1 for CountKSat.StepCount.holds_petals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:57:01.285662+00:00
-- url     : https://prove2.me/submissions/65a4c5fb-1009-4397-89b2-8b9f3266b133

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_Refine
import Mathlib.Tactic.Tauto
import Definitions.Def_CountKSat_StepCount
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog
open CountKSat.StepCount
namespace CountKSat.StepCount
theorem _root_.solution {v : PLit → Prop} {s P : PFml} {H : PCl} (hP : ∀ Q ∈ P, ∃ C ∈ s, ∀ l ∈ C, l ∈ H ∨ l ∈ Q)
    (hH : ¬ ∃ l ∈ H, v l) (hs : Holds v s) : Holds v P := by
  intro Q hQ
  obtain ⟨C, hC, hCQ⟩ := hP Q hQ
  obtain ⟨l, hl, hv⟩ := hs C hC
  rcases hCQ l hl with h | h
  · exact absurd ⟨l, h, hv⟩ hH
  · exact ⟨l, h, hv⟩
end CountKSat.StepCount
