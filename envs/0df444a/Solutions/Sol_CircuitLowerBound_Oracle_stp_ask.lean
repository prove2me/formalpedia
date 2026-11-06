-- Prove2me | solution 1 for CircuitLowerBound.Oracle.stp_ask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:47:03.040761+00:00
-- url     : https://prove2.me/submissions/674b8c3f-40ff-4d14-98b8-91da042178d3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_TM_Run
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Machine

set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Oracle
open ENP Turing Groundwork.TM
variable (M : TM2ComputableAux Bool Bool)
variable {M}
open Classical
namespace CircuitLowerBound.Oracle
theorem _root_.solution (O : Lang) (v : σ' M) (S : ∀ k, List (Γ' M k)) :
    stp M O ⟨some (.inr .ask), v, S⟩ =
      some ⟨some (if O ((S (.inl M.tm.k₁)).map M.outputAlphabet) then .inr .yes else .inr .no), v, Function.update S (.inl M.tm.k₁) []⟩ :=
  if_pos rfl
end CircuitLowerBound.Oracle
