-- Prove2me | solution 1 for CircuitLowerBound.Oracle.stp_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:27:10.53669+00:00
-- url     : https://prove2.me/submissions/a773bbf1-4485-41b5-b1f1-13b150ead9f7

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
namespace CircuitLowerBound.Oracle
theorem _root_.solution (O : Lang) {l : Λ' M} (hl : l ≠ .inr .ask) (v : σ' M) (S : ∀ k, List (Γ' M k)) :
    stp M O ⟨some l, v, S⟩ = some (TM2.stepAux (prog M l) v S) := by
  have h : (some l : Option (Λ' M)) ≠ some (.inr .ask) := fun h => hl (Option.some.inj h)
  exact if_neg h
end CircuitLowerBound.Oracle
