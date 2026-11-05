-- Prove2me | solution 1 for ClauseBound.Rec.CountRow.card_marked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:43:54.769606+00:00
-- url     : https://prove2.me/submissions/2674a43d-20d1-455f-90b7-c3e4d32e2b49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Rec_CountRow

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
open ClauseBound.Rec.CountRow
variable {δ : ℕ} (Ω : Fin δ → Type) [∀ b, Fintype (Ω b)] [∀ b, Nonempty (Ω b)] [∀ b, DecidableEq (Ω b)] (S : ∀ b, Finset (Ω b))
namespace ClauseBound.Rec.CountRow
theorem _root_.solution (b : Fin δ) :
    (#{ω : ∀ b, Ω b | ω b ∈ S b} : ℝ) = (Fintype.card (∀ b, Ω b) : ℝ) * ((#(S b) : ℝ) / Fintype.card (Ω b)) := by
  have h1 : #{ω : ∀ b, Ω b | ω b ∈ S b} = #(S b) * Fintype.card (∀ j : {j // j ≠ b}, Ω j) := by
    rw [← Finset.card_univ (α := ∀ j : {j // j ≠ b}, Ω j), ← Finset.card_product,
      ← Finset.card_map (Equiv.piSplitAt b Ω).toEmbedding]
    congr 1
    ext ⟨a, g⟩
    simp [Finset.mem_map_equiv]
  have h2 : Fintype.card (∀ b, Ω b) = Fintype.card (Ω b) * Fintype.card (∀ j : {j // j ≠ b}, Ω j) := by
    rw [Fintype.card_congr (Equiv.piSplitAt b Ω), Fintype.card_prod]
  have hc : (0 : ℝ) < Fintype.card (Ω b) := by exact_mod_cast Fintype.card_pos
  rw [h1, h2]
  push_cast
  field_simp
end ClauseBound.Rec.CountRow
