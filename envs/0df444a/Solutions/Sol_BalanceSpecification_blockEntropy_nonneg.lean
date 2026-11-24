-- Prove2me | solution 1 for BalanceSpecification.blockEntropy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:09:37.720649+00:00
-- url     : https://prove2.me/submissions/e84cf560-daaa-46ba-8c63-eda5444f0c4d

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_BlockEntropy

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
omit [DiscreteTopology A] [BorelSpace A]
namespace BalanceSpecification
theorem _root_.solution (μ : ProbabilityMeasure X.carrier) (n : ℕ) :
    0 ≤ blockEntropy μ n := by
  apply Finset.sum_nonneg
  intro w hw
  exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr measureReal_nonneg)
    (Real.log_nonpos measureReal_nonneg measureReal_le_one)
end BalanceSpecification
