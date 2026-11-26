-- Prove2me | solution 1 for C6BipartiteDomination.beta_ge_two_of_k_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:51:03.737852+00:00
-- url     : https://prove2.me/submissions/6a797eac-c43e-4c75-8e7e-a6c08bc36789

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
import Theorems.Thm_C6BipartiteDomination_beta_pos_of_mem_SPart
import Theorems.Thm_C6BipartiteDomination_bipartite_base_of_beta_eq_one
import Theorems.Thm_C6BipartiteDomination_lemma_7_1_odd_cycle
import Theorems.Thm_C6BipartiteDomination_mem_SPart
import Theorems.Thm_C6BipartiteDomination_mem_WBPart


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    {w : V} (hw : w ∈ SPart G D)
    (hk : 2 ≤ kCharge G D w) :
    2 ≤ betaCharge G D w := by
  by_contra h
  have hβ : betaCharge G D w = 1 := by
    have hpos := beta_pos_of_mem_SPart G hw
    omega
  have hwD : w ∉ D := by
    have hwWB := (mem_SPart G D w).mp hw |>.1
    exact (mem_WBPart G D w).mp hwWB |>.1
  have hbase := bipartite_base_of_beta_eq_one G hCan.1.2 hwD hβ
  exact (lemma_7_1_odd_cycle G hCan hw hk) hbase
end C6BipartiteDomination
