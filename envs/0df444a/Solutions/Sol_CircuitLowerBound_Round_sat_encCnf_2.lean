-- Prove2me | solution 2 for CircuitLowerBound.Round.sat_encCnf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:12:28.991055+00:00
-- url     : https://prove2.me/submissions/1180ea6b-bbac-4037-b79a-c1ca8f5b618d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_ENP_Round
import Theorems.Thm_CircuitLowerBound_Round_encCnf_injective

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Round
namespace CircuitLowerBound.Round
theorem _root_.solution (φ : Cnf) : SAT (encCnf φ) ↔ Sat φ :=
  ⟨fun ⟨_, h, hs⟩ => encCnf_injective h ▸ hs, fun h => ⟨φ, rfl, h⟩⟩
end CircuitLowerBound.Round
