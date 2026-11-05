-- Prove2me | solution 1 for ClauseBound.Part.Lower.sum_inv_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:31:52.331201+00:00
-- url     : https://prove2.me/submissions/60fe4fea-606f-46a1-adde-929dac13d10f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower
namespace ClauseBound.Part.Lower
theorem _root_.solution (K : ℕ) : ∑ k ∈ Ioc 0 K, 1 / (k : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 :=
  sum_le_hasSum _ (fun _ _ => by positivity) hasSum_zeta_two
end ClauseBound.Part.Lower
