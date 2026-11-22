-- Prove2me | solution 1 for GJKKL.sum_dv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:30.353304+00:00
-- url     : https://prove2.me/submissions/b0113c24-b150-4d3e-bb0f-34c4b9d9b895

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Theorems.Thm_GJKKL_sum_dv_eq
public import Theorems.Thm_GJKKL_avail_subset


set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) {k : ℕ} (hk : IsUniform H k) (h : List (Finset V)) :
    ∑ v, dv H h v = k * (avail H h).card := by
  rw [sum_dv_eq, sum_congr rfl fun e he => hk e (avail_subset H h he), sum_const, smul_eq_mul,
    mul_comm]
end GJKKL
