-- Prove2me | solution 1 for ClauseBound.Boson.Text.foldl_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:20:49.399927+00:00
-- url     : https://prove2.me/submissions/64acbaf9-ba31-4b27-8ecf-da4b22c965ec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Text
import Theorems.Thm_ClauseBound_Boson_Text_nabPos_smul

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset MvPolynomial
open ClauseBound.Boson.Text
namespace ClauseBound.Boson.Text
theorem _root_.solution (ks : List ℤ) : ∀ (c : ℤ) (f : Rg), ks.foldl (fun g k => nabPos k g) (c • f) = c • ks.foldl (fun g k => nabPos k g) f := by
  induction ks with
  | nil => intro c f; rfl
  | cons k ks ih => intro c f; rw [List.foldl_cons, List.foldl_cons, nabPos_smul, ih]
end ClauseBound.Boson.Text
