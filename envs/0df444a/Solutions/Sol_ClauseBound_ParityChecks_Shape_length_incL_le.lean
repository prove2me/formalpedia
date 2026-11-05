-- Prove2me | solution 1 for ClauseBound.ParityChecks.Shape.length_incL_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:31:05.965696+00:00
-- url     : https://prove2.me/submissions/1117a11d-7953-49a6-b9af-36f8f5ccf253

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_ClauseBound_ParityChecks_Shape_card_lam
import Theorems.Thm_ClauseBound_ParityChecks_Shape_getD_ok
import Theorems.Thm_ClauseBound_ParityChecks_Shape_length_le_of_nodup
import Theorems.Thm_ClauseBound_ParityChecks_Shape_length_incL
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks
variable {k n Δ : ℕ} {q : Par} {ψ : Fml} {Lam : List Chk} {j : ℕ}
namespace ClauseBound.ParityChecks.Shape
theorem _root_.solution (hnb : 1 ≤ q.nb) (h4 : q.m ≤ 2 * Δ * LD Δ * q.nb) (hj : j ≤ q.r) (hL : ∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < q.m)
    (hT : Tent q (lam q.m Lam)) : (incL n ψ Lam j).length ≤ 16 * Δ * LD Δ * q.r + q.m := by
  have h1 : ∑ j' ∈ range (j + 1), (Lam.getD j' []).length ≤ ∑ j' ∈ range (q.r + 1), (Lam.getD j' []).length :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
  have h2 : (Lam.getD q.r []).length ≤ q.m := length_le_of_nodup (getD_ok hL _).1 (getD_ok hL _).2
  have h3 : ∑ j' ∈ range q.r, (Lam.getD j' []).length = ∑ j' ∈ range q.r, #(lam q.m Lam j') :=
    Finset.sum_congr rfl fun j' _ => (card_lam Lam j' (getD_ok hL _).1 (getD_ok hL _).2).symm
  have hq : (0 : ℚ) < q.nb := by exact_mod_cast hnb
  have h5 : ((∑ j' ∈ range q.r, #(lam q.m Lam j') : ℕ) : ℚ) * q.nb < 8 * q.m * q.r + q.nb := by
    have h := mul_lt_mul_of_pos_right hT.inc hq
    have e : (8 * pr q.nb * q.m * q.r + 1) * (q.nb : ℚ) = 8 * q.m * q.r + q.nb := by
      unfold pr
      field_simp
    rwa [e] at h
  have h6 : (∑ j' ∈ range q.r, #(lam q.m Lam j')) * q.nb < 8 * q.m * q.r + q.nb := by exact_mod_cast h5
  have h7 : 8 * q.m * q.r ≤ 16 * Δ * LD Δ * q.r * q.nb := by
    calc 8 * q.m * q.r ≤ 8 * (2 * Δ * LD Δ * q.nb) * q.r := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h4)
      _ = 16 * Δ * LD Δ * q.r * q.nb := by ring
  have h8 : (∑ j' ∈ range q.r, #(lam q.m Lam j')) * q.nb < (16 * Δ * LD Δ * q.r + 1) * q.nb := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have h9 := Nat.lt_of_mul_lt_mul_right h8
  have h10 : ∑ j' ∈ range (q.r + 1), (Lam.getD j' []).length = ∑ j' ∈ range q.r, (Lam.getD j' []).length + (Lam.getD q.r []).length :=
    Finset.sum_range_succ _ _
  rw [length_incL]
  omega
end ClauseBound.ParityChecks.Shape
