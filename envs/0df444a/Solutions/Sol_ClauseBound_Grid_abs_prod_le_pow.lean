-- Prove2me | solution 1 for ClauseBound.Grid.abs_prod_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:42:01.816748+00:00
-- url     : https://prove2.me/submissions/6eaa8fbe-f38b-460b-a850-4529f056a00d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
namespace ClauseBound.Grid
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → ℤ) (B : ℕ) (h : ∀ i ∈ s, |f i| ≤ 2 ^ B) :
    |∏ i ∈ s, f i| ≤ 2 ^ (#s * B) := by
  calc |∏ i ∈ s, f i| = ∏ i ∈ s, |f i| := abs_prod _ _
    _ ≤ ∏ _i ∈ s, (2 : ℤ) ^ B := prod_le_prod (fun _ _ => abs_nonneg _) h
    _ = 2 ^ (#s * B) := by rw [prod_const, ← pow_mul, Nat.mul_comm]
end ClauseBound.Grid
