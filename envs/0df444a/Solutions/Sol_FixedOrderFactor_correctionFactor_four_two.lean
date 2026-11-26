-- Prove2me | solution 1 for FixedOrderFactor.correctionFactor_four_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:09:19.872791+00:00
-- url     : https://prove2.me/submissions/25cc3bda-4607-4b79-8916-9d9a20d57ee6

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_correctionFactor_four_two__91903136c5c9


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution : correctionFactor {two} 4 = 35 / 34 :=
  correctionFactor_four_two'
end FixedOrderFactor
