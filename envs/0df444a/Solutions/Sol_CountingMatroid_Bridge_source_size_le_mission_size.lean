-- Prove2me | solution 1 for CountingMatroid.Bridge.source_size_le_mission_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:35:44.622349+00:00
-- url     : https://prove2.me/submissions/d48fa752-e2de-4810-a9a0-7deca5d3e12c

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_Bridge_binaryNatLength_le_bits_length_add_one

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- The imported source size is at most six times the base used by the
original mission's polynomial resource bound. No matroid promise is needed. -/
theorem solution (n r : ℕ) (p : InputParams) :
    n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
      binaryNatLength (Nat.ceil p.δ⁻¹) + 1 ≤
    6 * (1 + n + OAI.CommonBasesFPRAS.inputLength n r p.ε p.δ +
      Nat.ceil p.ε⁻¹ + Nat.clog 2 (Nat.ceil p.δ⁻¹)) := by
  have hn := binaryNatLength_le_bits_length_add_one n
  have hr := binaryNatLength_le_bits_length_add_one r
  have heN := binaryNatLength_le_bits_length_add_one p.ε.num.natAbs
  have heD := binaryNatLength_le_bits_length_add_one p.ε.den
  have hdN := binaryNatLength_le_bits_length_add_one p.δ.num.natAbs
  have hdD := binaryNatLength_le_bits_length_add_one p.δ.den
  have hlog : binaryNatLength (Nat.ceil p.δ⁻¹) ≤
      Nat.clog 2 (Nat.ceil p.δ⁻¹) + 1 := by
    rw [binaryNatLength, Nat.log2_eq_log_two]
    exact Nat.add_le_add_right (Nat.log_le_clog _ _) 1
  unfold binaryInputLength binaryRatLength OAI.CommonBasesFPRAS.inputLength
  omega
