-- Prove2me | solution 1 for ClauseBound.Boson.Text.nabPos_mon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:22:52.081527+00:00
-- url     : https://prove2.me/submissions/36b866b3-ab54-43b4-971f-e33c9d2adf97

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Text
import Theorems.Thm_ClauseBound_Boson_Text_toFinsupp_erase

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset MvPolynomial
open ClauseBound.Boson.Text
namespace ClauseBound.Boson.Text
theorem _root_.solution (k : ℕ) (σ : Multiset ℕ) : nabPos (k : ℤ) (mon σ) = ((k : ℤ) * σ.count k) • mon (σ.erase k) := by
  unfold nabPos mon
  rw [Int.toNat_natCast, pderiv_monomial, toFinsupp_erase, Multiset.toFinsupp_apply, smul_monomial, smul_monomial]
  simp
end ClauseBound.Boson.Text
