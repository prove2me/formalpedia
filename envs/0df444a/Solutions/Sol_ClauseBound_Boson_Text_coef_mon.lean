-- Prove2me | solution 1 for ClauseBound.Boson.Text.coef_mon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:22:53.127372+00:00
-- url     : https://prove2.me/submissions/489d8c80-5869-4070-96ae-948ab3a91def

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
theorem _root_.solution (π σ : Multiset ℕ) : coef π (mon σ) = if π = σ then 1 else 0 := by
  unfold coef mon
  rw [coeff_monomial]
  by_cases h : π = σ
  · simp [h]
  · rw [if_neg h, if_neg]
    intro h'
    exact h (Multiset.toFinsupp.injective h'.symm)
end ClauseBound.Boson.Text
