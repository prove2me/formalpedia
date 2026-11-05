-- Prove2me | solution 1 for ClauseBound.Boson.Dual.pow_mul_factorial_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:46:57.910958+00:00
-- url     : https://prove2.me/submissions/86fc6df6-c618-4489-919f-d8bd73d63792

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Dual

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson ClauseBound.Boson.Dual
open Finset
namespace ClauseBound.Boson.Dual
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (m : ℕ) : k ^ m * m.factorial ∣ (m * k).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ((m + 1) * k).factorial = (m + 1) * k * ((m + 1) * k - 1).factorial :=
      (Nat.mul_factorial_pred (Nat.mul_ne_zero (Nat.succ_ne_zero m) (by omega))).symm
    have h2 : (m * k).factorial ∣ ((m + 1) * k - 1).factorial := Nat.factorial_dvd_factorial (by rw [Nat.succ_mul]; omega)
    rw [h1, pow_succ, Nat.factorial_succ]
    calc k ^ m * k * ((m + 1) * m.factorial) = (m + 1) * k * (k ^ m * m.factorial) := by ring
      _ ∣ _ := Nat.mul_dvd_mul_left _ (ih.trans h2)
end ClauseBound.Boson.Dual
