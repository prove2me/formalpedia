-- Prove2me | solution 1 for ClauseBound.ParityChecks.Start.start
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:21:52.473486+00:00
-- url     : https://prove2.me/submissions/2ee66d8a-02d5-4b00-820c-3bc5cd41a3bf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_ClauseBound_ParityChecks_Start
import Theorems.Thm_ClauseBound_ParityChecks_Start_pr_pos
import Theorems.Thm_ClauseBound_ParityChecks_Start_sum_omega_le
import Theorems.Thm_ClauseBound_ParityChecks_Start_Upar_fresh_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Start
open _root_.ParityChecks Finset
namespace ClauseBound.ParityChecks.Start
theorem _root_.solution : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r : ℕ), 2 ≤ nb → 1 ≤ r → 1 ≤ Fintype.card E →
    (5 / 8 : ℚ) ^ r * (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) ≤ 1 / 8 → Ups V nb r 0 (fun _ => ∅) univ ≤ 1 / 2 := by
  intro X E _ _ _ V nb r hnb hr hm hsmall
  have hp := pr_pos hnb
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  have hm' : (0 : ℚ) < Fintype.card E := by exact_mod_cast hm
  have h1 : Upar V nb r 0 (fun _ => ∅) univ ≤ 1 / 8 := by
    refine (Upar_fresh_le V nb r 0 (fun _ => ∅) hnb rfl).trans (le_trans ?_ hsmall)
    have e : (5 / 8 : ℚ) ^ r = (5 / 8) ^ (r - 1 - 0) * (5 / 8) := by
      rw [← pow_succ]; congr 1; omega
    rw [e, mul_assoc]
    simp only [range_zero, prod_empty, mul_one]
    have := sum_omega_le V nb
    gcongr
  have h2 : Uinc nb r 0 (fun _ => (∅ : Finset E)) univ = 1 / 8 := by
    unfold Uinc undRow
    simp only [card_empty, sum_const_zero, Nat.not_lt_zero, if_false, card_univ, ite_self, sum_const, card_range, smul_eq_mul]
    push_cast
    field_simp
    ring
  have h3 : Urow nb r 0 (fun _ => (∅ : Finset E)) univ = 1 / 8 := by
    unfold Urow undRow
    simp only [card_empty, Nat.not_lt_zero, if_false, card_univ, ite_self, Nat.sub_self, pow_zero, div_one, sum_const, card_range, nsmul_eq_mul, mul_one]
    field_simp
  have h4 : Ucol nb r 0 (fun _ => (∅ : Finset E)) univ = 1 / 8 := by
    have e : ∀ x : E, r - undCol r 0 univ x = 0 := by
      intro x; unfold undCol; simp only [mem_univ, if_true]; omega
    unfold Ucol
    simp only [e, notMem_empty, filter_false, card_empty, pow_zero, div_one, sum_const, card_univ, nsmul_eq_mul, mul_one]
    field_simp
  unfold Ups
  rw [h2, h3, h4]
  linarith
end ClauseBound.ParityChecks.Start
