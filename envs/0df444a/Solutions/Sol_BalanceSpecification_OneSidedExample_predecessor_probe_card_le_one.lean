-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.predecessor_probe_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:39.651024+00:00
-- url     : https://prove2.me/submissions/568345a0-cb5c-4ac6-b6ef-2c8886bcca9d

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Theorems.Thm_BalanceSpecification_OneSidedExample_predecessor_probe_subset

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) :
    (predecessorFinset (language shift) (probeWord n) n).card ≤ 1 := by
  exact (Finset.card_le_card (predecessor_probe_subset hn)).trans_eq (Finset.card_singleton _)
end BalanceSpecification.OneSidedExample
