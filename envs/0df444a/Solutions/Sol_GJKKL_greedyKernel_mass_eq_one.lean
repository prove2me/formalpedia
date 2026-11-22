-- Prove2me | solution 1 for GJKKL.greedyKernel_mass_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:04:16.083092+00:00
-- url     : https://prove2.me/submissions/e38826e3-d747-4a50-9fe4-4237fa629b3a

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
public import Theorems.Thm_GJKKL_greedyKernel_K
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil



set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution {H : Finset (Finset V)} {h : List (Finset V)}
    (hne : (avail H h).Nonempty) : ∑ a, (greedyKernel H).K h a = 1 := by
  simp only [greedyKernel_K]
  rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast (card_pos.mpr hne).ne')
end GJKKL
