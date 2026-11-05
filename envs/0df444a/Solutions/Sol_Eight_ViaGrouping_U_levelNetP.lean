-- Prove2me | solution 1 for Eight.ViaGrouping.U_levelNetP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:36:41.172249+00:00
-- url     : https://prove2.me/submissions/8ed6695d-1a9e-4120-ae42-51e1bc493968

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_StepMachines_Prog_GridDefs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_LevelNet
import Theorems.Thm_P2M_Eight_Level_U_netOf__16d6ae6630a8


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Finset Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution (g : ℕ) (tr : Bool) (lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) : (levelNetP g tr lam y Rm).U = totalG eightF g g tr 0 lam y := U_netOfι g tr lam y Rm
end Eight.ViaGrouping
