-- Prove2me | solution 1 for Erdos684.lt_obstructionModulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:48:46.395611+00:00
-- url     : https://prove2.me/submissions/1f900d4f-cf60-48ea-82e2-21a9d487f03b

module
public import Definitions.Def_Erdos684_Finite
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Definitions.Def_Erdos684_Lower

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos684
namespace Erdos684
theorem _root_.solution {K : ℕ} (hK : 2 < K) : K < obstructionModulus K := by
  apply (lt_primorial_self hK).trans_le
  exact Nat.le_mul_of_pos_left (primorial K) (Nat.lcmUpto_pos K)
end Erdos684
