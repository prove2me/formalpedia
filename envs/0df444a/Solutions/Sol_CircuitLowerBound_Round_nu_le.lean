-- Prove2me | solution 1 for CircuitLowerBound.Round.nu_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:01:00.884197+00:00
-- url     : https://prove2.me/submissions/3b273160-7d92-45b5-834b-474b96998275

import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Mathlib.Tactic

set_option autoImplicit false

open CircuitLowerBound
open ENP Groundwork

theorem solution (m : ℕ) : nu m ≤ m := by
  calc
    nu m ≤ (Nat.bits m).length :=
      (List.takeWhile_sublist (fun b => !b)).length_le
    _ = Nat.size m := Nat.size_eq_bits_len m
    _ ≤ m := Nat.size_le.mpr Nat.lt_two_pow_self
