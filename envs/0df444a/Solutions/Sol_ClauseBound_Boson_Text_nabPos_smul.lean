-- Prove2me | solution 1 for ClauseBound.Boson.Text.nabPos_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:15:54.593882+00:00
-- url     : https://prove2.me/submissions/eed58b39-cc9c-45d8-a2e9-34b31787dc34

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
theorem _root_.solution (k c : ℤ) (f : Rg) : nabPos k (c • f) = c • nabPos k f := by
  unfold nabPos
  rw [Derivation.map_smul, smul_comm]
end ClauseBound.Boson.Text
