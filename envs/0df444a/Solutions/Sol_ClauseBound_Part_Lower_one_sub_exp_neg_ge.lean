-- Prove2me | solution 1 for ClauseBound.Part.Lower.one_sub_exp_neg_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:31:19.296229+00:00
-- url     : https://prove2.me/submissions/be304b47-3717-4aaa-960a-a44383a8479d

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
theorem _root_.solution {y : ℝ} (hy : 0 ≤ y) (hy2 : y ≤ 2) : y / 3 ≤ 1 - Real.exp (-y) := by
  have h1 : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
  have h2 : Real.exp (-y) ≤ 1 / (y + 1) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by positivity) h1
  have h3 : 1 / (y + 1) ≤ 1 - y / 3 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith
end ClauseBound.Part.Lower
