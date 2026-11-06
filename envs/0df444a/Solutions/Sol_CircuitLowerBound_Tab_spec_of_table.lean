-- Prove2me | solution 1 for CircuitLowerBound.Tab.spec_of_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:30:49.749406+00:00
-- url     : https://prove2.me/submissions/3d79a74d-7da3-4ac1-9bf4-c60209fdf3ba

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
import Theorems.Thm_CircuitLowerBound_Tab_forall_fam
import Theorems.Thm_CircuitLowerBound_Tab_forall_flatten
import Theorems.Thm_CircuitLowerBound_Tab_bool_imp
import Theorems.Thm_CircuitLowerBound_Tab_bool_dec
import Theorems.Thm_CircuitLowerBound_Tab_bool_copy
import Theorems.Thm_CircuitLowerBound_Tab_or_self3
import Theorems.Thm_CircuitLowerBound_Tab_length_nxt_le
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
theorem _root_.solution {α : Atom N → ℕ → ℕ → Bool} {b Q P : ℕ} (H : ∀ c ∈ table N, HoldsC α b Q P c) : Spec N α b Q P := by
  classical
  have hQ : 0 < 2 ^ Q := by positivity
  have hb : 0 < 2 ^ b := by positivity
  simp only [table, forall_flatten, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, forall_fam] at H
  revert H
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28⟩
    simp only [HoldsC, holdsY, c1, c2, tval0, tval1, tval2, tval3, qval0, qval1, qval2, Nat.zero_add, Nat.add_zero, bool_imp, bool_dec, or_self3]
      at a1 a2 a3 a4 a5 a6 a7 a8 a9 a11 a12 a13 a14 a16 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27
    exact
      { preTop := fun t ht => a1 t ht 0 hQ
        preBot := fun t ht => a2 t ht 0 hQ
        preStep := fun t ht i => a3 i t ht 0 hQ
        csLab := fun t ht γ => a4 γ t ht 0 hQ
        csVar := fun t ht γ => a5 γ t ht 0 hQ
        csCell := fun t ht γ k j => a6 (γ, k, j) t ht 0 hQ
        nxLab := fun t ht γ x => a7 (γ, x) t ht 0 hQ
        nxVar := fun t ht γ x => a8 (γ, x) t ht 0 hQ
        nxLen := fun t ht γ k n => a9 (γ, k, n) t ht 0 hQ
        nxCell := fun t ht γ k x j hj => by
          have hj2 : j < 2 * dep N := lt_of_lt_of_le hj (length_nxt_le N γ k)
          have := a10 (γ, ⟨k, x⟩, ⟨j, hj2⟩)
          rw [if_pos hj] at this
          simpa only [HoldsC, holdsY, c2, tval1, tval2, qval0, Nat.zero_add, bool_imp, bool_dec] using this t ht 0 hQ
        copy := fun t ht q hq k n x => bool_copy.1 ⟨a11 (⟨k, x⟩, n) t ht q hq, a12 (⟨k, x⟩, n) t ht q hq⟩
        iLab := fun x => a13 x 0 hb 0 hQ
        iVar := fun x => a14 x 0 hb 0 hQ
        iCell := fun q hq k hk x => by
          have := a15 ⟨k, x⟩
          rw [if_pos hk] at this
          simpa only [HoldsC, holdsY, c1, tval0, qval1, Nat.add_zero, or_self3, bool_dec] using this 0 hb q hq
        iSome := fun q hq => a16 0 hb q hq
        iMost := fun q hq x x' hne => by
          have := a17 (x, x')
          rw [if_pos hne] at this
          have := this 0 hb q hq
          simp only [holdsY, c2, tval0, qval1, Nat.add_zero] at this
          tauto
        iBlank := fun q hq => a18 0 hb q hq
        uStep := fun q hq => a19 0 hb q hq
        uP := a20 0 hb 0 hQ
        uP1 := a21 0 hb 0 hQ
        uOne := fun q hq => a22 0 hb q hq
        cellP := a23 0 hb 0 hQ
        fLab := a24 0 hb 0 hQ
        fVar := a25 0 hb 0 hQ
        fOut0 := a26 0 hb 0 hQ
        fOut1 := a27 0 hb 0 hQ
        fOther := fun k hk => by
          have := a28 k
          rw [if_pos hk] at this
          simpa only [HoldsC, holdsY, c1, tval3, qval0, Nat.add_zero, or_self3] using this 0 hb 0 hQ }
end CircuitLowerBound.Tab
