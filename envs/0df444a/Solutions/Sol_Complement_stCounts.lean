-- Prove2me | solution 1 for Complement.stCounts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:43:47.726222+00:00
-- url     : https://prove2.me/submissions/f849e7da-1ba3-4180-b188-8deef55fd0a2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Complement_Defs
import Definitions.Def_Complement_Sets
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Cert
import Mathlib.Tactic
import Definitions.Def_Complement_Readers
import Theorems.Thm_Complement_stIndepAlone
import Theorems.Thm_Complement_stReaders
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Paper_Achievable_mono


set_option autoImplicit false
section
section
open Complement
open Groundwork Groundwork.Prog CountKSat GraphProblems
namespace Complement
theorem _root_.solution : StCounts := fun Z δ c hZ n G s hs => by
  obtain ⟨⟨r1, c1⟩, r2, c2⟩ := stReaders n G s hs
  constructor
  · obtain ⟨hsh, hl⟩ := stIndepAlone.2 n (matrix Gᶜ)
    obtain ⟨T, hr, hT⟩ := hZ n s _ hs hsh
    rw [← r1, c1] at hr
    exact ⟨T, (Stepped.mapIn_runs hr).mono le_rfl (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c)), hT⟩
  · obtain ⟨hsh, hl⟩ := stIndepAlone.2 n (matrix G)
    obtain ⟨T, hr, hT⟩ := hZ n (n - s) _ (Nat.sub_le n s) hsh
    rw [← r2, c2] at hr
    exact ⟨T, (Stepped.mapIn_runs hr).mono le_rfl (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c)), hT⟩
end Complement
