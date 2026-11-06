-- Prove2me | solution 1 for ExplicitCost.four_mul_div_g
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:19:35.873585+00:00
-- url     : https://prove2.me/submissions/16633308-4964-46fb-8387-f76949304a33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelBound
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution (hx : 1 ≤ x₀) (j : ℕ) : 4 * (g x₀ j ^ 4 / 4) = g x₀ j ^ 4 := by
  have h1 : 2 ∣ g x₀ j := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  have h2 : 2 ^ 4 ∣ g x₀ j ^ 4 := pow_dvd_pow_of_dvd h1 4
  exact Nat.mul_div_cancel' (Dvd.dvd.trans (by norm_num) h2)
end ExplicitCost
