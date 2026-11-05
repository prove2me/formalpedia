-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.numP_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:59:49.554795+00:00
-- url     : https://prove2.me/submissions/5cfddca2-0d30-42ce-bb82-f11686b0b66f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num
import Theorems.Thm_ClauseBound_ParityChecks_Num_list_sum_range

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
open ClauseBound.ParityChecks.Num
variable {q}
namespace ClauseBound.ParityChecks.Num
theorem _root_.solution (hnb : 1 ≤ q.nb) (A : ℤ) (B : ℕ → ℤ) :
    (q.numP A B : ℚ) = (q.nb : ℚ) ^ q.i₀ * ((A : ℚ) + ∑ i ∈ range (q.i₀ + 1), (-2 * pr q.nb) ^ i * (B i : ℚ)) := by
  have h0 : (q.nb : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.nb ≠ 0)
  unfold Par.numP
  rw [list_sum_range]
  push_cast
  rw [mul_add, Finset.mul_sum, mul_comm (A : ℚ)]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (mem_range.1 hi))
  rw [hd, Nat.add_sub_cancel_left, pow_add]
  unfold pr
  rw [mul_pow, one_div, inv_pow]
  field_simp
end ClauseBound.ParityChecks.Num
