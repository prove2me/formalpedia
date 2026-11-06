-- Prove2me | solution 1 for Eight.ViaGrouping.is_mono_B
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:42:16.149127+00:00
-- url     : https://prove2.me/submissions/8db951b2-8c0e-4a4e-814c-ca4ae47d91ae

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_StepMachines_Prog_GridDefs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_LevelNet
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Finset Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution {g P B B' : ℕ} {N : Net g} (h : N.Is P B) (hB : B ≤ B') : N.Is P B' :=
  have hp : (2 : ℤ) ^ B ≤ 2 ^ B' := pow_le_pow_right₀ (by norm_num) hB
  { h with
    B_pos := h.B_pos.trans hB
    ii_W := fun a z hz => (h.ii_W a z hz).trans_le hp
    ii_Ψ := fun a b hab z hz z' hz' => (h.ii_Ψ a b hab z hz z' hz').trans_le hp
    ii_f := fun a b hab z hz θ hθ => (h.ii_f a b hab z hz θ hθ).trans_le hp }
end Eight.ViaGrouping
