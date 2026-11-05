-- Prove2me | solution 1 for ClauseBound.Boson.Text.nord_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:23:08.956309+00:00
-- url     : https://prove2.me/submissions/b5b76251-4580-4fe8-bbc2-0b05d07ccdb5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Text
import Theorems.Thm_ClauseBound_Boson_Text_foldl_smul

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset MvPolynomial
open ClauseBound.Boson.Text
namespace ClauseBound.Boson.Text
theorem _root_.solution (ks : List ℤ) (c : ℤ) (f : Rg) : nord ks (c • f) = c • nord ks f := by
  unfold nord
  rw [foldl_smul, mul_smul_comm]
end ClauseBound.Boson.Text
