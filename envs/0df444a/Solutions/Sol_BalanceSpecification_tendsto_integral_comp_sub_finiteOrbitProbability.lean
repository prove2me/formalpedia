-- Prove2me | solution 1 for BalanceSpecification.tendsto_integral_comp_sub_finiteOrbitProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:02.734414+00:00
-- url     : https://prove2.me/submissions/21e3f280-8fb3-4e44-803d-414495e3e7c3

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Theorems.Thm_BalanceSpecification_norm_integral_comp_sub_finiteOrbitProbability

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter
open scoped Topology ENNReal Classical BoundedContinuousFunction
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [T2Space Ω]
    [HasOuterApproxClosed Ω]
    {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, Nonempty (I n)]
omit [HasOuterApproxClosed Ω]
namespace BalanceSpecification
theorem _root_.solution
    (f : Ω → Ω) (x : ∀ n, I n → Ω) (g : Ω →ᵇ ℝ) :
    Tendsto (fun n =>
      (∫ y, (g ∘ f) y ∂(finiteOrbitProbability f (x n) n : Measure Ω)) -
        ∫ y, g y ∂(finiteOrbitProbability f (x n) n : Measure Ω))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm
    (fun n => norm_integral_comp_sub_finiteOrbitProbability f (x n) n g)
  exact (tendsto_const_div_atTop_nhds_zero_nat (2 * ‖g‖)).comp (tendsto_add_atTop_nat 1)
end BalanceSpecification
