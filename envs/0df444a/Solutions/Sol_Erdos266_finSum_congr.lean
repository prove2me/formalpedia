-- Prove2me | solution 1 for Erdos266.finSum_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:56:27.23898+00:00
-- url     : https://prove2.me/submissions/3e6dbbce-f55a-4e61-8866-e06f190147c9

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {i k : ℕ} {S S' : ℕ → ℕ → ℤ}
    (h : ∀ l, l < k → ∀ j, j < dOf l → S l j = S' l j) :
    finSum i k S = finSum i k S' := by
  refine sum_congr rfl fun l hl => sum_congr rfl fun j hj => ?_
  rw [elemR, elemR, h l (mem_range.mp hl) j (mem_range.mp hj)]
end Erdos266
