-- Prove2me | solution 1 for Erdos684.obstructionModulus_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:48:35.43075+00:00
-- url     : https://prove2.me/submissions/aee5d4b8-b034-4eb9-81b5-1ba9eb50e878

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
theorem _root_.solution (K : ℕ) : 0 < obstructionModulus K :=
  Nat.mul_pos (Nat.lcmUpto_pos K) (primorial_pos K)
end Erdos684
