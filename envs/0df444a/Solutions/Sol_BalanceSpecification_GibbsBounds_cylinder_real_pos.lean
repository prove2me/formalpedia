-- Prove2me | solution 1 for BalanceSpecification.GibbsBounds.cylinder_real_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:36.450913+00:00
-- url     : https://prove2.me/submissions/71aca9b3-de61-4855-8999-21011364dd30

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Measures

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
    {w : Word A} (hw : w ∈ language X) :
    0 < (μ : Measure X.carrier).real (cylinder X w 0) := by
  have H := (div_pos zero_lt_one hB.1).trans_le (hB.2 w hw).1
  exact (mul_pos_iff_of_pos_right (Real.exp_pos _)).mp H
end GibbsBounds
end BalanceSpecification
