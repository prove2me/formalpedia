-- Prove2me | solution 1 for ClauseBound.ParityChecks.Shape.length_le_of_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:15:08.65739+00:00
-- url     : https://prove2.me/submissions/cd9a0dbf-e385-4df3-a4b6-20a1d7c29270

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks
namespace ClauseBound.ParityChecks.Shape
theorem _root_.solution {L : List ℕ} (hL : L.Nodup) {m : ℕ} (hm : ∀ x ∈ L, x < m) : L.length ≤ m := by
  rw [← List.toFinset_card_of_nodup hL, ← Finset.card_range m]
  exact Finset.card_le_card fun x hx => Finset.mem_range.2 (hm x (List.mem_toFinset.1 hx))
end ClauseBound.ParityChecks.Shape
