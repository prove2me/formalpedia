-- Prove2me | solution 1 for ExplicitCost.subst_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:44:24.219428+00:00
-- url     : https://prove2.me/submissions/ce456cc2-5fbe-4877-abc9-a4fee532d6bf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyRules

set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines QueryMachines.QueryMachine Printed
variable {Q Q' A A' C α α₁ α₂ β γ : Type} [Enc Q] [Enc Q'] [Enc A] [Enc A'] [Enc α] [Enc α₁] [Enc α₂] [Enc β] [Enc γ]
namespace ExplicitCost
theorem _root_.solution [HasSize C] [Enc C] [Carried C] {M : QueryMachine Q A α β} {N : QueryMachine Q' A' (C × Q) A} (hM : M.PolyTimeSteps) (hN : N.PolyTimeSteps) : (M.subst N).PolyTimeSteps := by
  obtain ⟨_⟩ := hM
  obtain ⟨_⟩ := hN
  exact ⟨subst_isPolyQ M N⟩
end ExplicitCost
