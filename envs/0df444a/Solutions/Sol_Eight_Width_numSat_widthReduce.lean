-- Prove2me | solution 1 for Eight.Width.numSat_widthReduce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:08:57.449199+00:00
-- url     : https://prove2.me/submissions/e0e9e7f7-bf7c-46e7-8faf-67a7a1d71590

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
import Theorems.Thm_Eight_Width_stRestrict
import Theorems.Thm_Eight_Width_stExtend

set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
variable {n : ℕ}
namespace Eight.Width
theorem _root_.solution (φ : CNF n) : SatK.numSat (widthReduce φ) = SatK.numSat φ := by
  unfold SatK.numSat
  refine Finset.card_bij (fun b _ i => b (Fin.castAdd (numFresh φ) i)) ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact stRestrict n φ b hb
  · intro b hb b' hb' e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb hb'
    exact (stExtend n φ _ (stRestrict n φ b hb)).unique ⟨hb, fun _ => rfl⟩ ⟨hb', fun i => (congrFun e i).symm⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨b, ⟨hb, e⟩, _⟩ := stExtend n φ a ha
    exact ⟨b, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hb, funext e⟩
end Eight.Width
