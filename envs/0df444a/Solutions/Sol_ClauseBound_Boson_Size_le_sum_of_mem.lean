-- Prove2me | solution 1 for ClauseBound.Boson.Size.le_sum_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:19:15.309822+00:00
-- url     : https://prove2.me/submissions/bb2c170a-0689-480d-9810-e58225a169cc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Rec_Window
import Definitions.Def_ClauseBound_Boson_Size

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Size
namespace ClauseBound.Boson.Size
theorem _root_.solution {π : Multiset ℕ} {l : ℕ} (h : l ∈ π) : l ≤ π.sum := by
  rw [← Multiset.sum_erase h]
  exact Nat.le_add_right _ _
end ClauseBound.Boson.Size
