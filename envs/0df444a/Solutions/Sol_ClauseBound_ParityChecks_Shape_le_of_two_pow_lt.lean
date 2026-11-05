-- Prove2me | solution 1 for ClauseBound.ParityChecks.Shape.le_of_two_pow_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:23:31.531183+00:00
-- url     : https://prove2.me/submissions/894b3fcd-8684-42f6-ad85-f250c47a876f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_ClauseBound_ParityChecks_Shape_pr_nonneg
import Theorems.Thm_ClauseBound_ParityChecks_Shape_pow_le_two_pow

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks
namespace ClauseBound.ParityChecks.Shape
theorem _root_.solution {nb a c N : ℕ} (hnb : 1 ≤ nb) (h : (2 : ℚ) ^ c < 2 * (8 * a * (1 + pr nb) ^ N)) :
    c ≤ Nat.clog 2 (16 * a) + 3 * N / (2 * nb) := by
  have hp := pr_nonneg nb
  have h1 : ((16 * a : ℕ) : ℚ) ≤ 2 ^ Nat.clog 2 (16 * a) := by exact_mod_cast Nat.le_pow_clog (by norm_num) _
  have h2 := pow_le_two_pow nb N hnb
  have h3 : (2 : ℚ) ^ c < 2 ^ (Nat.clog 2 (16 * a) + (3 * N / (2 * nb) + 1)) :=
    calc (2 : ℚ) ^ c < 2 * (8 * a * (1 + pr nb) ^ N) := h
      _ = ((16 * a : ℕ) : ℚ) * (1 + pr nb) ^ N := by push_cast; ring
      _ ≤ 2 ^ Nat.clog 2 (16 * a) * 2 ^ (3 * N / (2 * nb) + 1) := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := (pow_add _ _ _).symm
  have h4 := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).1 h3
  omega
end ClauseBound.ParityChecks.Shape
