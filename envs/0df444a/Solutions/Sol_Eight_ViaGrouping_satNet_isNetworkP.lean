-- Prove2me | solution 1 for Eight.ViaGrouping.satNet_isNetworkP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:17:56.39008+00:00
-- url     : https://prove2.me/submissions/cd9437f0-bd86-4ff8-8f3e-5de9bb5ac07c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_SatPsiDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_ToTuring_Poly_Count
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Theorems.Thm_Eight_ViaGrouping_satPsi_eq
import Theorems.Thm_Eight_ViaGrouping_satPsiM_runs
import Theorems.Thm_ClauseBound_Alg_GridPresents_presents
import Theorems.Thm_Eight_ViaGrouping_stBridge
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Prog_Count_sized_wordNet
import Theorems.Thm_Groundwork_Prog_presents
import Theorems.Thm_Groundwork_Prog_sized_mono
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_PaddedDescent_F_RebalF_presents
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.SatNet Eight.SecNetworks
variable {g k : ℕ} {Φ : Fml}
namespace Eight.ViaGrouping
theorem _root_.solution (hg : 0 < g) (k : ℕ) (Φ : Fml) :
    IsNetworkP (satProcs g k) Φ (satNet g k Φ) (satPf g k Φ) 1 1 (size Φ + 2 * g + 6 * (mu g Φ * k) + 8 + 2) ∧ (satNet g k Φ).value = (wordNet g k Φ).value ∧ (satNet g k Φ).U = (wordNet g k Φ).U :=
  stBridge Fml g (satP g k) (satPf g k) (satPsiM g k) Φ (wordNet g k Φ) (satPf g k Φ) 0 1 _ (le_max_left _ _) le_rfl
    ⟨sized_mono (sized_wordNet hg 0) (le_max_right _ _), presents hg Φ⟩ rfl
    fun a b hab z hz z' hz' => satPsi_eq hab z z' ▸ satPsiM_runs a b (mem_words.1 hz) (mem_words.1 hz')
end Eight.ViaGrouping
