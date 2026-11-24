-- Prove2me | solution 1 for BalanceSpecification.GibbsBounds.quasiBernoulli_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:10:15.801163+00:00
-- url     : https://prove2.me/submissions/5a3d935d-5bc3-4145-883b-1c2943d0155f

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Measures
public import Theorems.Thm_BalanceSpecification_cylinder_eq_empty_of_not_mem_language
public import Theorems.Thm_BalanceSpecification_GibbsBounds_quasiBernoulli

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
variable [Fintype A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
omit [DiscreteTopology A] [BorelSpace A]
namespace BalanceSpecification
namespace GibbsBounds
theorem _root_.solution {X : ShiftSpace A} {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} {K : ℝ} (hB : GibbsBounds hX μ K)
    (v w : Word A) :
    (μ : Measure X.carrier).real (cylinder X (v ++ w) 0) ≤
      K ^ 3 * (μ : Measure X.carrier).real (cylinder X v 0) *
        (μ : Measure X.carrier).real (cylinder X w 0) := by
  by_cases hvw : v ++ w ∈ language X
  · exact (hB.quasiBernoulli hvw).2
  · rw [cylinder_eq_empty_of_not_mem_language X hvw, measureReal_empty]
    exact mul_nonneg (mul_nonneg (pow_nonneg hB.1.le 3) measureReal_nonneg)
      measureReal_nonneg
end GibbsBounds
end BalanceSpecification
