-- Prove2me | solution 1 for ClauseBound.Boson.Scalars.choose_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:58:05.221875+00:00
-- url     : https://prove2.me/submissions/b1c5b555-d9a7-4588-90a2-60eff7b4d9e3

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
theorem _root_.solution {r : ℤ} {k : ℕ} (h0 : 0 ≤ r) (h : r < k) : Ring.choose r k = 0 := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by exact_mod_cast h)]
  simp
end ClauseBound.Boson.Scalars
