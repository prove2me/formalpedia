-- Prove2me | solution 1 for ClauseBound.Gen.Rate.col_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:54:39.266717+00:00
-- url     : https://prove2.me/submissions/dd0d7fb1-f248-432c-9311-63594409e926

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Rate
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K
import Theorems.Thm_ClauseBound_Gen_Rate_K_le_g
import Theorems.Thm_ClauseBound_Gen_Rate_size_le_self
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace ClauseBound.Gen.Rate
theorem _root_.solution (hx : 18 ≤ x₀) (l : ℕ) : ((g x₀ l * Nat.size (K x₀ l) : ℕ) : ℝ) ≤ (g x₀ l : ℝ) ^ 4 := by
  have n3 := big_le_K hx l
  have n4 := K_le_g x₀ l
  have h : g x₀ l * Nat.size (K x₀ l) ≤ g x₀ l ^ 4 := by
    calc g x₀ l * Nat.size (K x₀ l) ≤ g x₀ l * g x₀ l := Nat.mul_le_mul_left _ ((size_le_self _).trans n4)
      _ = g x₀ l ^ 2 := by ring
      _ ≤ g x₀ l ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  exact_mod_cast h
end ClauseBound.Gen.Rate
