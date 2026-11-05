-- Prove2me | solution 1 for CountKSat.Value.value_wordNet_eq_cntN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:10:06.121732+00:00
-- url     : https://prove2.me/submissions/508c00df-807c-49dc-b098-016456b58013

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_CountKSat_Value
import Theorems.Thm_CountKSat_Value_value_net_eq_cntN
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Count_le_mul_mu
import Theorems.Thm_Groundwork_Prog_Count_value_wordNet
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.SatNet
open CountKSat.Value
namespace CountKSat.Value
theorem _root_.solution {g k n : ℕ} (hg : 0 < g) {x : Fml} (hk : ∀ C ∈ x, C.length ≤ k)
    (hlt : ∀ C ∈ x, ∀ l ∈ C, l.1 < n) (hocc : ∀ i < n, ∃ C ∈ x, ∃ l ∈ C, l.1 = i) :
    (Count.wordNet g k x).value = cntN n x := by
  rw [Count.value_wordNet hg]
  exact value_net_eq_cntN hk (Count.le_mul_mu hg x) hlt hocc
end CountKSat.Value
