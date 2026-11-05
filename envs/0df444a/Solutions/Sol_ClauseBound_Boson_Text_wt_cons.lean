-- Prove2me | solution 1 for ClauseBound.Boson.Text.wt_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:20:27.818711+00:00
-- url     : https://prove2.me/submissions/72adf3cf-ea6f-45b2-8ba1-f705a8385508

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
theorem _root_.solution (n : ℕ) (a : List ℕ) (k : ℤ) (ks : List ℤ) : wt (n :: a) (k :: ks) = Ring.choose (-k - 1) (n - 1) * wt a ks := by
  simp [wt]
end ClauseBound.Boson.Text
