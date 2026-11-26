-- Prove2me | solution 1 for Erdos266.cnt_kOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:58:24.181997+00:00
-- url     : https://prove2.me/submissions/a518cb18-2f34-45d3-9383-38ea5679523f

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution (n : ℕ) : cnt (kOf n) ≤ n := by
  rcases Nat.eq_zero_or_pos (kOf n) with h | h
  · rw [h]
    simp [cnt]
  · have hmin := Nat.find_min (cnt_unbounded n) (show kOf n - 1 < kOf n by omega)
    rw [show kOf n - 1 + 1 = kOf n by omega] at hmin
    omega
end Erdos266
