-- Prove2me | solution 1 for ExplicitCost.isRect_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:54:23.658168+00:00
-- url     : https://prove2.me/submissions/50fed248-3eca-47b5-8697-739c6c850882

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PolyLists
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyQueries
import Theorems.Thm_ExplicitCost_colDiv_polyT
import Theorems.Thm_ExplicitCost_colMod_polyT

set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG Eight Eight.SecNetworks QueryMachines Printed
variable {α : Type} [Enc α]
namespace ExplicitCost
theorem _root_.solution {β : Type} [Enc β] : PolyT fun v : (Parent × β) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1) := PolyT.decide_lt colDiv_polyT colMod_polyT
end ExplicitCost
