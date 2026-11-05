-- Prove2me | solution 1 for Coding.getD_padOcc_occ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:14:49.397125+00:00
-- url     : https://prove2.me/submissions/1d7c553e-f2a1-4f9b-a3e5-cc272ccc2920

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLinks
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_Occ
import Theorems.Thm_Coding_getD_padOcc
import Theorems.Thm_Coding_place_sub
import Theorems.Thm_Coding_length_getD_le
import Theorems.Thm_Coding_mem_occIn
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution (h3 : ∀ C ∈ Φ, C.length ≤ 3) (a : Fin g) (z : List Bool) {o : ℕ × ℕ} (ho : o ∈ occOf g Φ a.val) :
    (padOcc g Φ a z).getD (place o - a.val * (mu g Φ * 3)) false = bitAt g Φ a.val z o := by
  obtain ⟨e, j⟩ := o
  have hm := mem_occIn.1 ho
  have h1 : a.val * mu g Φ ≤ e := hm.1
  have h2 : e < a.val * mu g Φ + mu g Φ := hm.2.1
  have h4 : j < (Φ.getD e []).length := hm.2.2
  have h5 := length_getD_le h3 e
  have e1 : ((e - a.val * mu g Φ) * 3 + j) / 3 = e - a.val * mu g Φ := by omega
  have e2 : ((e - a.val * mu g Φ) * 3 + j) % 3 = j := by omega
  have e3 : a.val * mu g Φ + (e - a.val * mu g Φ) = e := by omega
  rw [place_sub h1, getD_padOcc a z (by omega), e1, e2, e3, decide_eq_true h4, Bool.true_and]
end Coding
