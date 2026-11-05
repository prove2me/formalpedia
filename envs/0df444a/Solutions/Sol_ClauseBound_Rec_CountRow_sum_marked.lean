-- Prove2me | solution 1 for ClauseBound.Rec.CountRow.sum_marked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:46:28.090645+00:00
-- url     : https://prove2.me/submissions/56869441-2b82-4e3b-bc04-d004023efb38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Rec_CountRow
import Theorems.Thm_ClauseBound_Rec_CountRow_card_marked

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
open ClauseBound.Rec.CountRow
variable {δ : ℕ} (Ω : Fin δ → Type) [∀ b, Fintype (Ω b)] [∀ b, Nonempty (Ω b)] [∀ b, DecidableEq (Ω b)] (S : ∀ b, Finset (Ω b))
namespace ClauseBound.Rec.CountRow
theorem _root_.solution :
    ∑ ω : ∀ b, Ω b, (#{b | ω b ∈ S b} : ℝ) = (Fintype.card (∀ b, Ω b) : ℝ) * ∑ b, (#(S b) : ℝ) / Fintype.card (Ω b) := by
  have h (ω : ∀ b, Ω b) : (#{b | ω b ∈ S b} : ℝ) = ∑ b, if ω b ∈ S b then (1 : ℝ) else 0 := (Finset.sum_boole _ _).symm
  rw [Finset.sum_congr rfl fun ω _ => h ω, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_boole, card_marked]
end ClauseBound.Rec.CountRow
