-- Prove2me | solution 1 for ClauseBound.ParityChecks.prod_choose_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:56:12.336682+00:00
-- url     : https://prove2.me/submissions/9ae4ae8f-7071-4e7a-91ac-0cbfcba8d9a4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Theorems.Thm_ClauseBound_ParityChecks_Binom_choose_mul_choose_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Binom
namespace ClauseBound.ParityChecks
theorem _root_.solution {ι : Type} (s : Finset ι) (t μ : ι → ℕ) : ∏ i ∈ s, (t i).choose (μ i) ≤ (∑ i ∈ s, t i).choose (∑ i ∈ s, μ i) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
    rw [prod_cons, sum_cons, sum_cons]
    exact (Nat.mul_le_mul_left _ ih).trans (choose_mul_choose_le _ _ _ _)
end ClauseBound.ParityChecks
