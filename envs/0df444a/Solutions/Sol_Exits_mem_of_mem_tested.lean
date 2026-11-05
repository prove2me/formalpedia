-- Prove2me | solution 1 for Exits.mem_of_mem_tested
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:56:56.771855+00:00
-- url     : https://prove2.me/submissions/eb80d940-f4af-4b76-9b66-2a107c45a27a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Defs
import Definitions.Def_Exits_Tested

set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Stepped
variable {α β γ τ ν : Type}
namespace Exits
theorem _root_.solution {v : ν → Bool} {l : List ν} {x : ν} (h : x ∈ tested v l) : x ∈ l := List.mem_of_mem_take h
end Exits
