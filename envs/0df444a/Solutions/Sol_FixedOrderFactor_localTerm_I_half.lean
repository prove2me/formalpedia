-- Prove2me | solution 1 for FixedOrderFactor.localTerm_I_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:09:24.875945+00:00
-- url     : https://prove2.me/submissions/3433832a-6866-421d-9b95-12d691493156

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_localTerm_I_half__1a94193266fb


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution : localTerm Complex.I (1 / 2) = 4 / 5 ∧
    localTerm (-Complex.I) (1 / 2) = 4 / 5 :=
  localTerm_I_half'
end FixedOrderFactor
