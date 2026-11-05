-- Prove2me | solution 1 for ClauseBound.Part.Upper.sqrt_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:27:13.895538+00:00
-- url     : https://prove2.me/submissions/c59b7e8f-e3d4-4887-8ecc-9fe94fd20e07

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
theorem _root_.solution {n x : ℝ} (hn : 0 < n) (hx : x ≤ n) : Real.sqrt (n - x) ≤ Real.sqrt n - x / (2 * Real.sqrt n) := by
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hss : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  have h1 : x / (2 * Real.sqrt n) ≤ Real.sqrt n / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine Real.sqrt_le_iff.2 ⟨by linarith, ?_⟩
  have h2 : (Real.sqrt n - x / (2 * Real.sqrt n)) ^ 2 = n - x + (x / (2 * Real.sqrt n)) ^ 2 := by
    rw [sub_sq, hss]
    field_simp
  rw [h2]
  nlinarith [sq_nonneg (x / (2 * Real.sqrt n))]
end ClauseBound.Part.Upper
