-- Prove2me | solution 1 for ClauseBound.Boson.Size.sum_mul_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:49:17.673318+00:00
-- url     : https://prove2.me/submissions/9f60782e-073c-481e-9d8b-e0fec4ddabfe

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
theorem _root_.solution (σ : Multiset ℕ) : ∑ k ∈ σ.toFinset, (k : ℤ) * (σ.count k : ℤ) = (σ.sum : ℤ) := by
  conv_rhs => rw [Finset.sum_multiset_count σ]
  push_cast
  exact sum_congr rfl fun k _ => by rw [smul_eq_mul, Nat.cast_mul, mul_comm]
end ClauseBound.Boson.Size
