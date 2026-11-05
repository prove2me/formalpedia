-- Prove2me | solution 1 for ClauseBound.Boson.Text.mem_tup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:25:03.357071+00:00
-- url     : https://prove2.me/submissions/9573b8bf-10e0-4c0a-a508-dbd7c42af2ce

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Text
import Theorems.Thm_ClauseBound_Boson_Text_mem_win

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset MvPolynomial
open ClauseBound.Boson.Text
namespace ClauseBound.Boson.Text
theorem _root_.solution {M : ℕ} : ∀ {q : ℕ} {ks : List ℤ}, ks ∈ tup M q ↔ ks.length = q ∧ ∀ k ∈ ks, k ≠ 0 ∧ -(M : ℤ) ≤ k ∧ k ≤ M
  | 0, ks => by
    simp only [tup, mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.1 h
  | q + 1, ks => by
    simp only [tup, mem_image, mem_product, Prod.exists]
    constructor
    · rintro ⟨k, ks', ⟨h1, h2⟩, rfl⟩
      obtain ⟨h3, h4⟩ := solution.1 h2
      refine ⟨by simp [h3], fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact mem_win.1 h1
      · exact h4 x hx
    · rintro ⟨h1, h2⟩
      rcases ks with _ | ⟨k, ks'⟩
      · simp at h1
      · exact ⟨k, ks', ⟨mem_win.2 (h2 k (by simp)), solution.2 ⟨by simpa using h1, fun x hx => h2 x (by simp [hx])⟩⟩, rfl⟩
end ClauseBound.Boson.Text
