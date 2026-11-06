-- Prove2me | solution 1 for Coding.stOccNetIs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:02:59.199617+00:00
-- url     : https://prove2.me/submissions/d06cc885-c0cd-4d40-a9d8-b36981e7ce7e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Occ
import Definitions.Def_Coding_Padding
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Coding_OccMore
import Theorems.Thm_Coding_length_occIn_le
import Theorems.Thm_Coding_abs_boole_lt
import Theorems.Thm_Coding_capF_eq
import Theorems.Thm_Coding_testsBetween_comm
import Theorems.Thm_Groundwork_Grid_boole_congr
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Count_boole_congr
import Theorems.Thm_Groundwork_Prog_Count_le_mul_mu
import Theorems.Thm_Groundwork_Prog_Count_sized_wordNet
import Theorems.Thm_Groundwork_mem_words
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution : StOccNetIs := by
  intro g Φ hg hΦ h3
  have hμ : 0 < mu g Φ := by
    have h1 := le_mul_mu hg Φ
    have h2 : 0 < Φ.length := List.length_pos_iff.2 hΦ
    rcases Nat.eq_zero_or_pos (mu g Φ) with h | h
    · rw [h, Nat.mul_zero] at h1
      omega
    · exact h
  refine ⟨by omega, le_rfl, fun a z hz => mem_words.1 hz, fun a => ?_, fun a b _ z _ z' _ => boole_congr eq_comm, fun a b => congrArg List.length (testsBetween_comm a.val b.val), fun a b _ z _ z' _ => ?_, fun a => ?_,
    fun _ _ _ => abs_boole_lt _, fun _ _ _ _ _ _ _ => abs_boole_lt _, fun _ _ _ _ _ _ _ => abs_boole_lt _⟩
  · have := length_occIn_le h3 (a.val * mu g Φ) (mu g Φ)
    change (occIn Φ (a.val * mu g Φ) (mu g Φ)).length ≤ 6 * mu g Φ
    omega
  · change (if restrict g Φ a.val b.val z = restrict g Φ b.val a.val z' then (1 : ℤ) else 0)
      = ∑ θ ∈ words (testsBetween g Φ a.val b.val).length, (if restrict g Φ a.val b.val z = θ then (1 : ℤ) else 0) * (if restrict g Φ b.val a.val z' = θ then 1 else 0)
    rw [Finset.sum_eq_single (restrict g Φ a.val b.val z)]
    · rw [if_pos rfl, one_mul]
      exact boole_congr eq_comm
    · intro θ _ hne
      rw [if_neg (Ne.symm hne), zero_mul]
    · intro h
      exact absurd (mem_words.2 (List.length_map _)) h
  · have h := (sized_wordNet (k := 3) (φ := Φ) hg 0).sum_c a
    have e : ∑ b ∈ univ.erase a, (occNet g Φ).c a b = ∑ b ∈ univ.erase a, (wordNet g 3 Φ).c a b := Finset.sum_congr rfl fun b _ => (capF_eq hg h3 a.val b.val).symm
    rw [e]
    omega
end Coding
