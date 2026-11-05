-- Prove2me | solution 1 for ClauseBound.ParityChecks.Binom.choose_mul_choose_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:54:53.975417+00:00
-- url     : https://prove2.me/submissions/0bcad53c-72b5-4a5a-a339-6883649fca1d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Binom

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open ClauseBound.ParityChecks.Binom
namespace ClauseBound.ParityChecks.Binom
theorem _root_.solution (a b i j : ℕ) : a.choose i * b.choose j ≤ (a + b).choose (i + j) := by
  rw [Nat.add_choose_eq]
  exact single_le_sum (f := fun ij : ℕ × ℕ => a.choose ij.1 * b.choose ij.2) (fun _ _ => Nat.zero_le _) (mem_antidiagonal.2 (rfl : (i, j).1 + (i, j).2 = i + j))
end ClauseBound.ParityChecks.Binom
