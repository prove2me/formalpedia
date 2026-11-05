-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertLib.clog_two_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:43:14.952819+00:00
-- url     : https://prove2.me/submissions/c0d3e384-baf4-4a92-9b12-8213d5089127

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertLib
theorem _root_.solution (n : ℕ) : Nat.clog 2 n = Nat.size (n - 1) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · rw [Nat.clog_of_right_le_one (by omega)]
    have : n - 1 = 0 := by omega
    rw [this, Nat.size_zero]
  · refine le_antisymm ?_ ?_
    · rw [Nat.clog_le_iff_le_pow (by norm_num)]
      have := Nat.lt_size_self (n - 1)
      omega
    · rw [Nat.size_le]
      have := Nat.le_pow_clog (b := 2) (by norm_num) n
      omega
end ClauseBound.ParityChecks.CertLib
