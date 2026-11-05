-- Prove2me | solution 1 for ClauseBound.Boson.Half.two_pow_lt_big
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:54:40.064293+00:00
-- url     : https://prove2.me/submissions/af4edc1f-f1ad-423e-8aa2-6ed7ab18afef

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_ClauseBound_Boson_HalfSum
import Definitions.Def_ClauseBound_Rec_Number
import Definitions.Def_ClauseBound_Boson_Half
import Theorems.Thm_ClauseBound_Boson_Half_eL_add_eR_lt

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Half
namespace ClauseBound.Boson.Half
theorem _root_.solution {h e : ℕ} (he : e ≤ eL h + eR h) : (2 : ℤ) ^ e < 2 ^ big h :=
  pow_lt_pow_right₀ (by norm_num) (by have := eL_add_eR_lt h; unfold big; omega)
end ClauseBound.Boson.Half
