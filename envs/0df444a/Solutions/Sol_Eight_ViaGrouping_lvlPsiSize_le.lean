-- Prove2me | solution 1 for Eight.ViaGrouping.lvlPsiSize_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:42:23.675488+00:00
-- url     : https://prove2.me/submissions/45638d76-3901-423f-bfd5-92c36de8cd70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_StepMachines_Prog_GridDefs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_LevelNet

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Finset Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution (g sc B n sy B' : ℕ) (hn : 1 ≤ n) (hy : sy ≤ 2 * nRect g * n + 1) (hB' : B' ≤ g * B + g ^ 2 * n) :
    sc + sy + 2 * size g + 4 * (g ^ 3 * n) + B' + 8 ≤ lvlPsiSize g * (sc + B + n) := by
  have h1 : lvlPsiSize g * (sc + B + n) = 2 * nRect g * n + 2 * size g * n + 4 * (g ^ 3 * n) + g * B + g ^ 2 * n + 10 * n + 10 * sc
      + ((2 * nRect g + 2 * size g + 4 * g ^ 3 + g + g ^ 2) * sc + (2 * nRect g + 2 * size g + 4 * g ^ 3 + g ^ 2 + 10) * B + g * n) := by
    unfold lvlPsiSize
    ring
  have h2 : 2 * size g ≤ 2 * size g * n := Nat.le_mul_of_pos_right _ hn
  omega
end Eight.ViaGrouping
