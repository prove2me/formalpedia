-- Prove2me | solution 1 for ClauseBound.Gen.Rate.one_le_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:54:26.746031+00:00
-- url     : https://prove2.me/submissions/655820fc-9b42-42f2-b415-ca14e29ed8ea

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Rate
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace ClauseBound.Gen.Rate
theorem _root_.solution (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) : 1 ≤ Real.logb 2 ((K x₀ l : ℝ) * (lam + B)) := by
  have h1 : 2 ≤ K x₀ l * (lam + B) := by
    have := big_le_K hx l
    calc 2 ≤ K x₀ l := by omega
      _ ≤ K x₀ l * (lam + B) := Nat.le_mul_of_pos_right _ (by omega)
  have h2 : (2 : ℝ) ≤ (K x₀ l : ℝ) * (lam + B) := by exact_mod_cast h1
  have h3 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) h2
  rwa [Real.logb_self_eq_one (by norm_num)] at h3
end ClauseBound.Gen.Rate
