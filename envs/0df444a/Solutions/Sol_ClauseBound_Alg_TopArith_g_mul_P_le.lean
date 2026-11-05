-- Prove2me | solution 1 for ClauseBound.Alg.TopArith.g_mul_P_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:34:46.813299+00:00
-- url     : https://prove2.me/submissions/8eaac1a0-af78-4915-a069-bb6fc03c6bfe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_TopArith
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.TopArith
open PaddedDescent.F
variable {K k m : ℕ}
namespace ClauseBound.Alg.TopArith
theorem _root_.solution (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) : 3 * K ^ 8 * PtopK (3 * K ^ 8) k m ≤ 5 * (k * m) := by
  have hg : 2 * (3 * K ^ 8) ≤ 3 * m := by
    have : 2 * K ^ 8 ≤ K ^ 9 := by rw [pow_succ K 8, mul_comm]; exact Nat.mul_le_mul_left _ hK
    omega
  have hK8 : 0 < K ^ 8 := by positivity
  generalize 3 * K ^ 8 = g at hg ⊢
  have hq : g * ((m + g - 1) / g) ≤ m + g := (Nat.mul_div_le _ _).trans (by omega)
  have hkm : m ≤ k * m := Nat.le_mul_of_pos_left _ hk
  have hkg : 2 * (k * g) ≤ 3 * (k * m) := by
    calc 2 * (k * g) = k * (2 * g) := by ring
      _ ≤ k * (3 * m) := Nat.mul_le_mul_left _ hg
      _ = 3 * (k * m) := by ring
  unfold PtopK
  rcases max_cases 1 (2 * k * ((m + g - 1) / g)) with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]; omega
  · rw [h]
    calc g * (2 * k * ((m + g - 1) / g)) = 2 * k * (g * ((m + g - 1) / g)) := by ring
      _ ≤ 2 * k * (m + g) := Nat.mul_le_mul_left _ hq
      _ = 2 * (k * m) + 2 * (k * g) := by ring
      _ ≤ 5 * (k * m) := by omega
end ClauseBound.Alg.TopArith
