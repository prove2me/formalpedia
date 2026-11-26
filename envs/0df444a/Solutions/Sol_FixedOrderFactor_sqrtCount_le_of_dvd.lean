-- Prove2me | solution 1 for FixedOrderFactor.sqrtCount_le_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:11:23.31761+00:00
-- url     : https://prove2.me/submissions/1dcfda34-f5f9-4bfb-8097-a7f332bf0edc

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_sqrtCount_le_of_dvd__c2eccb1785d4


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (M a : ℕ) {s s' : ℕ} (h : s' ∣ s) :
    sqrtCount M a s ≤ sqrtCount M a s' :=
  sqrtCount_le_of_dvd' M a h
end FixedOrderFactor
