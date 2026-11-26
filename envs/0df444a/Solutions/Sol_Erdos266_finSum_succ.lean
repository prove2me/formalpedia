-- Prove2me | solution 1 for Erdos266.finSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:56:17.069734+00:00
-- url     : https://prove2.me/submissions/e74fff5e-3763-45c5-b961-baed111e456c

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (i k : ℕ) (S : ℕ → ℕ → ℤ) :
    finSum i (k + 1) S = finSum i k S + ∑ j ∈ range (dOf k), f (i + 1) (elemR S k j) :=
  sum_range_succ _ k
end Erdos266
