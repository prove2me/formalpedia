-- Prove2me | solution 1 for ClauseBound.Gen.Rate.two_lam_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:54:27.781195+00:00
-- url     : https://prove2.me/submissions/31aa93c9-41e5-4f1d-96a1-2dd11d3b178d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Rate
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K
import Theorems.Thm_ClauseBound_Gen_Rate_K_le_g

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace ClauseBound.Gen.Rate
theorem _root_.solution (hx : 18 ≤ x₀) (l lam B : ℕ) : 2 * lam ≤ g x₀ l ^ 2 * (lam + B) := by
  have h1 := big_le_K hx l
  have h2 := K_le_g x₀ l
  have h3 : 2 ≤ g x₀ l ^ 2 := by
    calc 2 ≤ g x₀ l := by omega
      _ ≤ g x₀ l ^ 2 := Nat.le_self_pow two_ne_zero _
  calc 2 * lam ≤ g x₀ l ^ 2 * lam := Nat.mul_le_mul_right _ h3
    _ ≤ g x₀ l ^ 2 * (lam + B) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
end ClauseBound.Gen.Rate
