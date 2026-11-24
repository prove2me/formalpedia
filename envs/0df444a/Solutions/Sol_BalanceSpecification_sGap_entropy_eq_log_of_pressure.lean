-- Prove2me | solution 1 for BalanceSpecification.sGap_entropy_eq_log_of_pressure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:21.344829+00:00
-- url     : https://prove2.me/submissions/d6b575d0-e2a6-48cb-ab46-55876dad0485

module
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Definitions.Def_BalanceSpecificaton_GrowthUpperBounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Theorems.Thm_BalanceSpecification_sGap_partial_pressure_le_one
public import Theorems.Thm_BalanceSpecification_log_le_sGap_entropy_of_pressure
public import Theorems.Thm_BalanceSpecification_entropy_le_log_of_polynomial_wordCount_bound
public import Theorems.Thm_BalanceSpecification_sGapShift_nonempty
public import Theorems.Thm_BalanceSpecification_sGap_wordCount_le_polynomial_pow


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter Set
open scoped Topology
namespace BalanceSpecification
theorem _root_.solution [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) {β : ℝ} (hβ : 1 < β)
    (hroot : HasSum (fun s : S => (β⁻¹)^(s.val + 1)) 1) :
    entropy (sGapShift S) (sGapShift_nonempty hS) = Real.log β := by
  apply le_antisymm
  · apply entropy_le_log_of_polynomial_wordCount_bound (sGapShift_nonempty hS)
      (zero_lt_one.trans hβ)
    exact sGap_wordCount_le_polynomial_pow hS hβ
      (sGap_partial_pressure_le_one (zero_lt_one.trans hβ) hroot)
  · exact log_le_sGap_entropy_of_pressure hS hβ hroot
end BalanceSpecification
