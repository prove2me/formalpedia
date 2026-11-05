-- Prove2me | solution 1 for ClauseBound.Boson.Text.sum_win
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:15:29.568013+00:00
-- url     : https://prove2.me/submissions/db6c77b3-58f3-4668-ab4a-cf7d1c5d2478

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Text

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset MvPolynomial
open ClauseBound.Boson.Text
namespace ClauseBound.Boson.Text
theorem _root_.solution (M : ℕ) (G : ℤ → ℤ) : ∑ k ∈ win M, G k = ∑ l ∈ Icc 1 M, G (-(l : ℤ)) + ∑ k ∈ Icc 1 M, G (k : ℤ) := by
  unfold win
  rw [sum_union, sum_image, sum_image]
  · intro x _ y _ h; simpa using h
  · intro x _ y _ h; simpa using h
  · rw [disjoint_left]
    intro x hx hy
    obtain ⟨l, hl, rfl⟩ := mem_image.1 hx
    obtain ⟨k, hk, h⟩ := mem_image.1 hy
    have := (mem_Icc.1 hl).1
    have := (mem_Icc.1 hk).1
    omega
end ClauseBound.Boson.Text
