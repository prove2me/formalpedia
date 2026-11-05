-- Prove2me | solution 1 for ClauseBound.Boson.Text.coef_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:21:33.823112+00:00
-- url     : https://prove2.me/submissions/d04684e6-128a-4578-b142-a72fa8acf4aa

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
theorem _root_.solution (π : Multiset ℕ) (l : ℕ) (f : Rg) : coef π (X l * f) = if l ∈ π then coef (π.erase l) f else 0 := by
  unfold coef
  rw [coeff_X_mul', Multiset.toFinsupp_support, toFinsupp_erase]
  simp only [Multiset.mem_toFinset]
end ClauseBound.Boson.Text
