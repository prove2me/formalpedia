-- Prove2me | solution 1 for Complement.stFromSized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:04:05.342393+00:00
-- url     : https://prove2.me/submissions/aadab4e8-5067-433e-a5fc-e3fd579dedf2

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
import Theorems.Thm_Complement_stReadersCert
import Theorems.Thm_Complement_stCounts

set_option autoImplicit false
section
section
open Complement
open Groundwork Groundwork.Prog CountKSat GraphProblems
namespace Complement
theorem _root_.solution : StFromSized := fun hS δ hδ => by
  obtain ⟨Z, ⟨hZp⟩, c, hc⟩ := hS 2 δ hδ
  exact ⟨Z, ⟨IsPolyT.mapIn stReadersCert.1⟩, ⟨IsPolyT.mapIn stReadersCert.2⟩, c, stCounts Z δ c hc⟩
end Complement
