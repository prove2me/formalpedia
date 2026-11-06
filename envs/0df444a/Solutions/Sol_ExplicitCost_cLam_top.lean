-- Prove2me | solution 1 for ExplicitCost.cLam_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:42:34.530275+00:00
-- url     : https://prove2.me/submissions/df9901a1-729f-4251-bee3-58db07dfc318

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_EndBounds
import Definitions.Def_CountedRecursion_CliqueReads
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_EndCounted
import Theorems.Thm_ExplicitCost_length_unary


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (l lam B : ℕ) : cLam (top l lam B) = lam := length_unary lam
end ExplicitCost
