-- Prove2me | solution 1 for ClauseBound.Part.Upper.sum_inv_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:27:25.007885+00:00
-- url     : https://prove2.me/submissions/cb2f53a0-dbdd-4c1b-a368-72ce2f96d17d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Upper

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Upper
namespace ClauseBound.Part.Upper
theorem _root_.solution (s : Finset ℕ) : ∑ k ∈ s, 1 / (k : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 :=
  sum_le_hasSum s (fun _ _ => by positivity) hasSum_zeta_two
end ClauseBound.Part.Upper
