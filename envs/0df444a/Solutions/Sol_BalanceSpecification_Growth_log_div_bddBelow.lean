-- Prove2me | solution 1 for BalanceSpecification.Growth.log_div_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:52:20.09023+00:00
-- url     : https://prove2.me/submissions/5586e3c7-fad9-4ad9-aaf2-ebb884714bcc

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Growth

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.Growth
namespace BalanceSpecification.Growth
theorem _root_.solution {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n) :
    BddBelow (range fun n : ℕ => Real.log (a n) / n) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact div_nonneg (Real.log_nonneg (ha n)) (Nat.cast_nonneg n)
end BalanceSpecification.Growth
