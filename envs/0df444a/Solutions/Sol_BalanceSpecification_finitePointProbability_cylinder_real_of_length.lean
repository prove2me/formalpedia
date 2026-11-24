-- Prove2me | solution 1 for BalanceSpecification.finitePointProbability_cylinder_real_of_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:09.211806+00:00
-- url     : https://prove2.me/submissions/32ebca1d-f1cd-4c9e-bcbe-747bc7f2eba9

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Theorems.Thm_BalanceSpecification_finitePointProbability_cylinder_real

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter
open scoped Topology ENNReal Classical BoundedContinuousFunction
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution
    {M : ℕ} (u : Word A) (a b : ℕ) (hM : M = a + u.length + b)
    [Nonempty ↥(wordFinset (language X) M)]
    (x : ↥(wordFinset (language X) M) → X.carrier)
    (hx : ∀ w, block (x w).val 0 M = w.val) :
    (finitePointProbability (fun w => (shiftMap X)^[a] (x w)) : Measure X.carrier).real
        (cylinder X u 0) =
      ((occurrenceFinset (language X) u a b).card : ℝ) / wordCount (language X) M := by
  subst M
  exact finitePointProbability_cylinder_real u a b x hx
end BalanceSpecification
