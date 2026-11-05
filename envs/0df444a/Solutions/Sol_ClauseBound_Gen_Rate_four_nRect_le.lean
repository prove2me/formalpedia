-- Prove2me | solution 1 for ClauseBound.Gen.Rate.four_nRect_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:41:12.643907+00:00
-- url     : https://prove2.me/submissions/82ffa6a6-868e-44bf-9e70-caf65715bbf9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_RateAux

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Nat (size)
namespace ClauseBound.Gen.Rate
theorem _root_.solution (g : ℕ) : 4 * ClauseBound.Alg.nRectG g g ≤ g ^ 4 := by
  have h1 : 2 * Groundwork.Grid.c2 g ≤ g * g := by
    unfold Groundwork.Grid.c2
    calc 2 * (g * (g - 1) / 2) ≤ g * (g - 1) := Nat.mul_div_le _ _
      _ ≤ g * g := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  unfold ClauseBound.Alg.nRectG
  calc 4 * (Groundwork.Grid.c2 g * Groundwork.Grid.c2 g) = (2 * Groundwork.Grid.c2 g) * (2 * Groundwork.Grid.c2 g) := by ring
    _ ≤ (g * g) * (g * g) := Nat.mul_le_mul h1 h1
    _ = g ^ 4 := by ring
end ClauseBound.Gen.Rate
