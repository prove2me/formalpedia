-- Prove2me | solution 1 for ClauseBound.Boson.Text.toFinsupp_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:20:26.107905+00:00
-- url     : https://prove2.me/submissions/ce7eb2ad-0f44-4095-8ee4-2ab076c78df7

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
theorem _root_.solution (π : Multiset ℕ) (l : ℕ) : Multiset.toFinsupp (π.erase l) = Multiset.toFinsupp π - Finsupp.single l 1 := by
  ext x
  rw [Finsupp.coe_tsub, Pi.sub_apply, Multiset.toFinsupp_apply, Multiset.toFinsupp_apply]
  by_cases h : x = l
  · subst h
    rw [Multiset.count_erase_self, Finsupp.single_eq_same]
  · rw [Multiset.count_erase_of_ne h, Finsupp.single_eq_of_ne h, Nat.sub_zero]
end ClauseBound.Boson.Text
