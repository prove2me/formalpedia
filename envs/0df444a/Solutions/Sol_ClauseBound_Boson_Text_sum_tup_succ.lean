-- Prove2me | solution 1 for ClauseBound.Boson.Text.sum_tup_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:15:42.625693+00:00
-- url     : https://prove2.me/submissions/2092c4b5-b702-4705-9874-5c558fa20ae7

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
theorem _root_.solution (M q : ℕ) (G : List ℤ → ℤ) : ∑ ks ∈ tup M (q + 1), G ks = ∑ k ∈ win M, ∑ ks ∈ tup M q, G (k :: ks) := by
  rw [tup, sum_image, sum_product]
  rintro ⟨k, ks⟩ _ ⟨k', ks'⟩ _ h
  simp only [List.cons.injEq] at h
  exact Prod.ext h.1 h.2
end ClauseBound.Boson.Text
