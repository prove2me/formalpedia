-- Prove2me | solution 1 for ClauseBound.Boson.Scalars.succ_mul_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:00:16.780533+00:00
-- url     : https://prove2.me/submissions/79f5a171-31e9-4886-9c7c-6332fc8b757d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Scalars

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson ClauseBound.Boson.Scalars
open Finset
namespace ClauseBound.Boson.Scalars
theorem _root_.solution (r : ℤ) (n : ℕ) : ((n : ℤ) + 1) * Ring.choose r (n + 1) = r * Ring.choose (r - 1) n := by
  have h := Ring.choose_smul_choose r (n := n + 1) (k := 1) (by omega)
  simpa [Ring.choose_one_right] using h
end ClauseBound.Boson.Scalars
