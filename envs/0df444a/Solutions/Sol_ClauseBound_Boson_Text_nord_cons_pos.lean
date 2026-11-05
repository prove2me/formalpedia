-- Prove2me | solution 1 for ClauseBound.Boson.Text.nord_cons_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:23:20.629216+00:00
-- url     : https://prove2.me/submissions/b402ceae-12cc-401f-a67d-27b8018b9d5f

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
theorem _root_.solution {k : ℤ} (hk : 0 < k) (ks : List ℤ) (f : Rg) : nord (k :: ks) f = nord ks (nabPos k f) := by
  unfold nord
  rw [List.filter_cons_of_neg (by simp; omega), List.filter_cons_of_pos (by simpa using hk), List.foldl_cons]
end ClauseBound.Boson.Text
