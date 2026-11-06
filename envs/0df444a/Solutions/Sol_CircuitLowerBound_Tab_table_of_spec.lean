-- Prove2me | solution 1 for CircuitLowerBound.Tab.table_of_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:31:58.322653+00:00
-- url     : https://prove2.me/submissions/b32e6ab5-8965-4e68-801f-404425484560

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Table
import Theorems.Thm_CircuitLowerBound_Tab_tval0
import Theorems.Thm_CircuitLowerBound_Tab_tval1
import Theorems.Thm_CircuitLowerBound_Tab_tval2
import Theorems.Thm_CircuitLowerBound_Tab_tval3
import Theorems.Thm_CircuitLowerBound_Tab_qval0
import Theorems.Thm_CircuitLowerBound_Tab_qval1
import Theorems.Thm_CircuitLowerBound_Tab_qval2
import Theorems.Thm_CircuitLowerBound_Tab_holdsC_taut
import Theorems.Thm_CircuitLowerBound_Tab_forall_fam
import Theorems.Thm_CircuitLowerBound_Tab_forall_flatten
import Theorems.Thm_CircuitLowerBound_Tab_bool_imp
import Theorems.Thm_CircuitLowerBound_Tab_bool_dec
import Theorems.Thm_CircuitLowerBound_Tab_bool_copy
import Theorems.Thm_CircuitLowerBound_Tab_or_self3
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool)
variable {N}
variable (N) [Finite (Case N)] [∀ k, Finite (N.tm.Γ k)]
variable {N}
namespace CircuitLowerBound.Tab
theorem _root_.solution {α : Atom N → ℕ → ℕ → Bool} {b Q P : ℕ} (h : Spec N α b Q P) : ∀ c ∈ table N, HoldsC α b Q P c := by
  classical
  simp only [table, forall_flatten, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, forall_fam]
  · simp only [HoldsC, holdsY, c1, c2, tval0, tval1, tval2, tval3, qval0, qval1, qval2, Nat.zero_add, Nat.add_zero, bool_imp, bool_dec, or_self3]
    refine ⟨fun t ht _ _ => h.preTop t ht, fun t ht _ _ => h.preBot t ht, fun i t ht _ _ => h.preStep t ht i, fun γ t ht _ _ => h.csLab t ht γ,
      fun γ t ht _ _ => h.csVar t ht γ, fun p t ht _ _ => h.csCell t ht p.1 p.2.1 p.2.2, fun p t ht _ _ => h.nxLab t ht p.1 p.2,
      fun p t ht _ _ => h.nxVar t ht p.1 p.2, fun p t ht _ _ => h.nxLen t ht p.1 p.2.1 p.2.2, fun p => ?_, fun p t ht q hq => ?_, fun p t ht q hq => ?_,
      fun x _ _ _ _ => h.iLab x, fun x _ _ _ _ => h.iVar x, fun p => ?_, fun _ _ q hq => h.iSome q hq, fun p => ?_, fun _ _ q hq => h.iBlank q hq,
      fun _ _ q hq => h.uStep q hq, fun _ _ _ _ => h.uP, fun _ _ _ _ => h.uP1, fun _ _ q hq => h.uOne q hq, fun _ _ _ _ => h.cellP,
      fun _ _ _ _ => h.fLab, fun _ _ _ _ => h.fVar, fun _ _ _ _ => h.fOut0, fun _ _ _ _ => h.fOut1, fun k => ?_⟩
    · split_ifs with hj
      · intro t ht q _
        simp only [tval1, tval2, qval0, Nat.zero_add, bool_imp, bool_dec]
        exact h.nxCell t ht p.1 p.2.1.1 p.2.1.2 p.2.2 hj
      · exact holdsC_taut α b Q P
    · exact (bool_copy.2 (h.copy t ht q hq p.1.1 p.2 p.1.2)).1
    · exact (bool_copy.2 (h.copy t ht q hq p.1.1 p.2 p.1.2)).2
    · split_ifs with hk
      · intro t _ q hq
        simp only [tval0, qval1, Nat.add_zero, or_self3, bool_dec]
        exact h.iCell q hq p.1 hk p.2
      · exact holdsC_taut α b Q P
    · split_ifs with hne
      · intro t _ q hq
        simp only [tval0, qval1, Nat.add_zero]
        have := h.iMost q hq p.1 p.2 hne
        tauto
      · exact holdsC_taut α b Q P
    · split_ifs with hk
      · intro t _ q _
        simp only [tval3, qval0, Nat.add_zero, or_self3]
        exact h.fOther k hk
      · exact holdsC_taut α b Q P
end CircuitLowerBound.Tab
