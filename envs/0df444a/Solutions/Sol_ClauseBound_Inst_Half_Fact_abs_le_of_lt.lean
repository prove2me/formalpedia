-- Prove2me | solution 1 for ClauseBound.Inst.Half.Fact.abs_le_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:15:59.873566+00:00
-- url     : https://prove2.me/submissions/d980c7ed-0dac-4fde-b20a-83d7675ac3eb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfFact

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Finset
open ClauseBound.Inst.Half.Fact
namespace ClauseBound.Inst.Half.Fact
theorem _root_.solution {h i : ℕ} (hi : i < 4 * h + 1) : |(i : ℤ) - 2 * h| ≤ 2 * (h : ℤ) := abs_le.2 ⟨by omega, by omega⟩
end ClauseBound.Inst.Half.Fact
