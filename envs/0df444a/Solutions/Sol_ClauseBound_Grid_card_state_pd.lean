-- Prove2me | solution 1 for ClauseBound.Grid.card_state_pd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:34:28.107857+00:00
-- url     : https://prove2.me/submissions/d6b399bd-7ced-4c03-acd4-c726ce0827d5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [DecidableEq α]
namespace ClauseBound.Grid
theorem _root_.solution {p d L : ℕ} (hρ : Fintype.card ρ = p) (hγ : Fintype.card γ = d) (hα : Fintype.card α = 2 ^ L) :
    Fintype.card (RowSt ρ γ α) = 2 ^ (p * d ^ 2 * L) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_prod, hα, hρ, hγ, ← pow_mul, ← pow_mul]
  congr 1
  ring
end ClauseBound.Grid
