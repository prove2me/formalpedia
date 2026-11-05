-- Prove2me | solution 1 for ClauseBound.Group.Grouping.exists_perm_of_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:58:06.696448+00:00
-- url     : https://prove2.me/submissions/efed7566-ce71-4b0f-b929-8a0376ffe9b6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Group_Sample
import Definitions.Def_ClauseBound_Group_Grouping

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Group
open Finset
open ClauseBound.Group.Grouping
namespace ClauseBound.Group.Grouping
theorem _root_.solution {V C : Type} [Fintype V] [DecidableEq C] (α β : V → C) (h : ∀ y, #{x | α x = y} = #{x | β x = y}) :
    ∃ p : Equiv.Perm V, ∀ x, β (p x) = α x := by
  have hy : ∀ y, Nonempty ({x // α x = y} ≃ {x // β x = y}) := fun y =>
    ⟨Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact h y)⟩
  refine ⟨(Equiv.sigmaFiberEquiv α).symm.trans ((Equiv.sigmaCongrRight fun y => (hy y).some).trans (Equiv.sigmaFiberEquiv β)), fun x => ?_⟩
  exact ((hy (α x)).some ⟨x, rfl⟩).2
end ClauseBound.Group.Grouping
