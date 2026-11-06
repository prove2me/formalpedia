-- Prove2me | solution 1 for ExplicitCost.exponent_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:16:32.152318+00:00
-- url     : https://prove2.me/submissions/b0b9d1cc-09cd-4202-a24b-dfa834dcdaf7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_ChainLabel
import Definitions.Def_CountedRecursion_CrudeBounds
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_CountedRecursion_PartAPrinted
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Chain

set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
namespace ExplicitCost
theorem _root_.solution {e0 r G4 Λ cc lg k2 kk x : ℝ} (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) (hkk : 0 < kk) (hcl : 0 ≤ cc / 4 * G4 * lg) (hk2 : 0 ≤ k2) (h : x ≤ r * (G4 * Λ) + cc / 4 * G4 * lg + k2) :
    e0 * x + 3 * (G4 * Λ) / kk ≤ (r * e0 + 3 / kk) * G4 * Λ + cc / 4 * G4 * lg + k2 := by
  have h1 := mul_le_mul_of_nonneg_left h he0
  have h2 : e0 * (cc / 4 * G4 * lg) ≤ cc / 4 * G4 * lg := by nlinarith
  have h3 : e0 * k2 ≤ k2 := by nlinarith
  have e : (r * e0 + 3 / kk) * G4 * Λ = e0 * (r * (G4 * Λ)) + 3 * (G4 * Λ) / kk := by
    field_simp
  rw [e]
  nlinarith
end ExplicitCost
