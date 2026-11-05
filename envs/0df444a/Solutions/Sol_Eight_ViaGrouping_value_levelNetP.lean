-- Prove2me | solution 1 for Eight.ViaGrouping.value_levelNetP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:18:13.201268+00:00
-- url     : https://prove2.me/submissions/162aa328-54e8-4d57-bc64-1d88d499e0cc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_StepMachines_Prog_GridDefs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_LevelNet
import Theorems.Thm_P2M_Eight_Level_value_netOf__39744228d791


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Finset Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution {lam : ℕ} (hlam : 1 ≤ lam) (g : ℕ) (tr : Bool) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    (levelNetP g tr lam y Rm).value = Zι (gridR0 g g lam Rm) (Level.patOf g lam y) := value_netOfι hlam g tr y Rm
end Eight.ViaGrouping
