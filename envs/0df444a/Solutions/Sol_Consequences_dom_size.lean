-- Prove2me | solution 1 for Consequences.dom_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:30:41.815678+00:00
-- url     : https://prove2.me/submissions/b58e3770-6558-4e3e-879f-6ec5751ae151

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Consequences_Defs
import Definitions.Def_Consequences_Sets
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_DomTree
import Definitions.Def_CountKSat_Walk
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Consequences_Dom
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Consequences
open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify CountKSat GraphProblems Paper SplitCount
namespace Consequences
theorem _root_.solution {w c n X : ℕ} (hX : X = n + 2) :
    (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) + 1 + (X + (c * (4 * X) ^ c + 1)) + 1 ≤ (8 * w + 40 + c * 4 ^ c + c + 4) * X ^ (8 * w + 40 + c * 4 ^ c + c + 4) := by
  obtain ⟨K, hK⟩ : ∃ K, K = 8 * w + 40 + c * 4 ^ c := ⟨_, rfl⟩
  rw [← hK]
  have hX1 : 1 ≤ X := by omega
  obtain ⟨P, hP⟩ : ∃ P, P = X ^ (c + 4) := ⟨_, rfl⟩
  have hP1 : X ≤ P := by rw [hP]; exact Nat.le_self_pow (by omega) X
  have hP4 : X ^ 4 ≤ P := by rw [hP]; exact Nat.pow_le_pow_right hX1 (by omega)
  have hPc : X ^ c ≤ P := by rw [hP]; exact Nat.pow_le_pow_right hX1 (by omega)
  have a1 : (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) ≤ (8 * w + 26) * P := by
    have h3 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ hX1
    calc (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) ≤ (2 * X) * ((4 * w + 13) * X ^ 3) := by
          refine Nat.mul_le_mul (by omega) ?_
          have : (4 * w + 13) * X ^ 3 = (4 * w + 12) * X ^ 3 + X ^ 3 := by ring
          omega
      _ = (8 * w + 26) * X ^ 4 := by ring
      _ ≤ (8 * w + 26) * P := Nat.mul_le_mul_left _ hP4
  have a2 : c * (4 * X) ^ c ≤ c * 4 ^ c * P := by
    rw [mul_pow, ← mul_assoc]
    exact Nat.mul_le_mul_left _ hPc
  have total : (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) + 1 + (X + (c * (4 * X) ^ c + 1)) + 1 ≤ K * P := by
    have eK : K * P = (8 * w + 26) * P + c * 4 ^ c * P + 14 * P := by rw [hK]; ring
    omega
  refine total.trans ?_
  rw [hP]
  exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hX1 (by omega))
end Consequences
