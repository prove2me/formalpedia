-- Prove2me | solution 1 for CountingMatroid.Bridge.binaryNatLength_le_bits_length_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:33:43.655426+00:00
-- url     : https://prove2.me/submissions/3979ae0d-aad7-4d9e-8187-0bf7f6f156c6

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- The source counts a zero digit; the mission uses the possibly empty
binary list. The conventions differ by at most one bit per natural number. -/
theorem solution (n : ℕ) :
    binaryNatLength n ≤ n.bits.length + 1 := by
  rw [binaryNatLength, Nat.size_eq_bits_len, Nat.log2_eq_log_two]
  by_cases hn : n = 0
  · subst n; simp
  · have := Nat.log_lt_of_lt_pow hn (Nat.lt_size_self n)
    omega
