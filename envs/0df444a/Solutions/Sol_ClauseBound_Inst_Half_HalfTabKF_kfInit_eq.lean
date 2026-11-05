-- Prove2me | solution 1 for ClauseBound.Inst.Half.HalfTabKF.kfInit_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:24:57.057194+00:00
-- url     : https://prove2.me/submissions/80db6a2a-4d3f-44ca-a46a-cd6cf58b916a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Definitions.Def_ClauseBound_Boson_KF
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
open ClauseBound.Inst.Half.HalfTabKF
namespace ClauseBound.Inst.Half.HalfTabKF
theorem _root_.solution (h : ℕ) (flat : List (List ℕ)) :
    kfInit h flat = (List.range (h + 1)).map fun w => tab flat fun π σ => if w = 0 then (if π = σ then 1 else 0) else 0 := by
  unfold kfInit oneT
  refine List.map_congr_left fun w _ => ?_
  split_ifs <;> rfl
end ClauseBound.Inst.Half.HalfTabKF
