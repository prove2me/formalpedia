-- Prove2me | solution 1 for GJKKL.sum_uncovered_dv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:23.095494+00:00
-- url     : https://prove2.me/submissions/81e6084a-8010-4c20-9231-a90dfad5b59c

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Theorems.Thm_GJKKL_dv_eq_zero_of_covered
public import Theorems.Thm_GJKKL_sum_dv

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) {k : ℕ} (hk : IsUniform H k)
    (h : List (Finset V)) :
    ∑ v ∈ uncovered h, dv H h v = k * (avail H h).card := by
  rw [← sum_dv H hk h, uncovered, ← sum_sdiff (subset_univ (covered h)),
    sum_eq_zero (fun v hv => dv_eq_zero_of_covered hv), add_zero]
end GJKKL
