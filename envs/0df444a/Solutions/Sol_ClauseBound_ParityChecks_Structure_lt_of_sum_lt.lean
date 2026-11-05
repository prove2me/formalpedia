-- Prove2me | solution 1 for ClauseBound.ParityChecks.Structure.lt_of_sum_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:15:20.31485+00:00
-- url     : https://prove2.me/submissions/dcc3bbb2-e276-48c5-b2df-73795c6f1f5a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_ClauseBound_ParityChecks_Structure

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Structure
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Structure
theorem _root_.solution {ι : Type} (s : Finset ι) (a b : ι → ℚ) (c B : ℚ) (hc : 0 < c) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i)
    (hB : ∀ i ∈ s, b i ≤ B) (h : 1 / c * ∑ i ∈ s, a i / b i < 1) {i : ι} (hi : i ∈ s) : a i < c * B := by
  have h1 : a i / b i ≤ ∑ i ∈ s, a i / b i :=
    single_le_sum (f := fun i => a i / b i) (fun k hk => div_nonneg (ha k hk) (hb k hk).le) hi
  have h2 : ∑ i ∈ s, a i / b i < c := by
    rwa [one_div, inv_mul_lt_iff₀ hc, mul_one] at h
  have h3 : a i < c * b i := (div_lt_iff₀ (hb i hi)).1 (h1.trans_lt h2)
  exact h3.trans_le (mul_le_mul_of_nonneg_left (hB i hi) hc.le)
end ClauseBound.ParityChecks.Structure
