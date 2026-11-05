-- Prove2me | solution 1 for ClauseBound.Grid.value_rowNet_tr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:43:48.491965+00:00
-- url     : https://prove2.me/submissions/bb45549f-cd6b-419d-9161-bd37598e8c12

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_ClauseBound_Grid_Expand
import Theorems.Thm_Groundwork_Grid_ZG_tr
import Theorems.Thm_Groundwork_Grid_value_rowNet


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
namespace ClauseBound.Grid
theorem _root_.solution {G : Rect ρ γ → α → α → α → α → ℤ} {C : Rect γ ρ → Cut α τ} (h : ∀ ω, (C ω).Factors (trG G ω))
    (R : Inst (ρ × γ) α) (t₀ : τ) (L : ℕ) : (rowNet (trInst R) C t₀ L).value = ZG R G := by
  rw [← ZG_tr]
  exact value_rowNet h (trInst R) t₀ L
end ClauseBound.Grid
