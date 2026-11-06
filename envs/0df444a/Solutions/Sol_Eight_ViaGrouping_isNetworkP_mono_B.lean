-- Prove2me | solution 1 for Eight.ViaGrouping.isNetworkP_mono_B
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:51:39.450963+00:00
-- url     : https://prove2.me/submissions/52753553-2fc6-477c-bea5-5a131bf2cc6e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_StepMachines_Prog_GridDefs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_LevelNet
import Theorems.Thm_Eight_ViaGrouping_is_mono_B

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Finset Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution {C : Type} {g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B B' τ S : ℕ} (h : IsNetworkP Np c N P B τ S) (hB : B ≤ B') : IsNetworkP Np c N P B' τ S :=
  ⟨is_mono_B h.is hB, h.τ_pos, h.given⟩
end Eight.ViaGrouping
