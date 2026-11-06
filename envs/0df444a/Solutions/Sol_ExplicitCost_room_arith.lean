-- Prove2me | solution 1 for ExplicitCost.room_arith
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:21:02.379098+00:00
-- url     : https://prove2.me/submissions/7930f64a-80af-4795-9093-fa794497d73b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverCall
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverRoom
import Theorems.Thm_ExplicitCost_pw_add
import Theorems.Thm_ExplicitCost_pw_mul
import Theorems.Thm_ExplicitCost_pw_num
import Theorems.Thm_ExplicitCost_pw_pow
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (c Cn Cg : ℕ) : ∃ C : ℕ, ∀ X g K p l lam B m n A : ℕ, 2 ≤ X → g * g ≤ X → K ≤ g → p ≤ g → l ≤ g → 2 * lam ≤ X → B ≤ X → m ≤ X ^ c → n ≤ m → A ≤ X ^ (c + 4) →
    20 * (Cn * g + (2 * l + 2 * lam + 2 * B + 2 * p + 2 * K + (n * (m + 2) + 1) + (m + 1) + 2 * (n * (2 * lam + 2) + 1) + 9) + (X * (c * g ^ 4) + 2) + (X * (c * g ^ 4) + (A + g * A) + 2) + (A + (l + 9)) ^ Cg +
      (A + g * A) + (K * g + 2) + g + A + (g ^ 4 * lam + g * A) + 4) ≤ X ^ C := by
  apply Exists.intro
  intro X g K p l lam B m n A hX hgg hK hp hl hlam hB hm hn hA
  have hXX : X ≤ X ^ 1 := (pow_one X).ge
  have hg : g ≤ X ^ 1 := ((Nat.le_mul_self g).trans hgg).trans hXX
  have hKx := hK.trans hg
  have hpx := hp.trans hg
  have hlx := hl.trans hg
  have h2lam := hlam.trans hXX
  have hlamx : lam ≤ X ^ 1 := le_trans (by omega) h2lam
  have hBx := hB.trans hXX
  have hnx := hn.trans hm
  have hg4 : g ^ 4 ≤ X ^ 2 := by
    calc g ^ 4 = (g * g) * (g * g) := by ring
      _ ≤ X * X := Nat.mul_le_mul hgg hgg
      _ = X ^ 2 := (sq X).symm
  have u6 := pw_add hX (pw_mul hnx (pw_add hX hm (pw_num hX 2))) (pw_num hX 1)
  have u7 := pw_add hX hm (pw_num hX 1)
  have u8 := pw_mul (pw_num hX 2) (pw_add hX (pw_mul hnx (pw_add hX h2lam (pw_num hX 2))) (pw_num hX 1))
  have t2 := pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_mul (pw_num hX 2) hlx) h2lam) (pw_mul (pw_num hX 2) hBx)) (pw_mul (pw_num hX 2) hpx)) (pw_mul (pw_num hX 2) hKx)) u6) u7) u8) (pw_num hX 9)
  have e0 := pw_mul hXX (pw_mul (pw_num hX c) hg4)
  have gA := pw_mul hg hA
  have G := pw_add hX hA gA
  have t5 := pw_pow (pw_add hX hA (pw_add hX hlx (pw_num hX 9))) Cg
  exact pw_mul (pw_num hX 20) (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_mul (pw_num hX Cn) hg) t2) (pw_add hX e0 (pw_num hX 2)))
    (pw_add hX (pw_add hX e0 G) (pw_num hX 2))) t5) G) (pw_add hX (pw_mul hKx hg) (pw_num hX 2))) hg) hA) (pw_add hX (pw_mul hg4 hlamx) gA)) (pw_num hX 4))
end ExplicitCost
