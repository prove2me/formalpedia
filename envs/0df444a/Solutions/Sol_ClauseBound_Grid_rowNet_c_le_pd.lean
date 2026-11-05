-- Prove2me | solution 1 for ClauseBound.Grid.rowNet_c_le_pd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:15:48.676816+00:00
-- url     : https://prove2.me/submissions/0ad992d5-9485-4a7e-a086-cb0b076f5961

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size
import Theorems.Thm_Groundwork_Grid_rowNet_c_le


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
namespace ClauseBound.Grid
theorem _root_.solution {d L m : ℕ} (hm : 1 ≤ m) (hγ : Fintype.card γ = d) (R : Inst (ρ × γ) α) (C : Rect ρ γ → Cut α τ)
    (t₀ : τ) (hcap : ∀ ω, (C ω).cap ≤ 2 * m * L) (a b : ρ) : (rowNet R C t₀ L).c a b ≤ d ^ 2 * (m * L) :=
  rowNet_c_le hm hγ R C t₀ hcap a b
end ClauseBound.Grid
