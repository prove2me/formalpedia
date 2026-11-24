-- Prove2me | solution 1 for BalanceSpecification.IsGibbsMeasure.cylinder_real_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:08:21.338802+00:00
-- url     : https://prove2.me/submissions/ba12fe14-de0f-485d-80f7-5e759a7c4e35

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Measures
public import Theorems.Thm_BalanceSpecification_IsInvariant_cylinder_real_eq_zero
public import Theorems.Thm_BalanceSpecification_GibbsBounds_cylinder_real_pos

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
variable [Fintype A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
namespace BalanceSpecification
namespace IsGibbsMeasure
theorem _root_.solution {X : ShiftSpace A}
    {hX : X.carrier.Nonempty} {μ : ProbabilityMeasure X.carrier}
    (hG : IsGibbsMeasure hX μ) {w : Word A} (hw : w ∈ language X) (k : ℤ) :
    0 < (μ : Measure X.carrier).real (cylinder X w k) := by
  obtain ⟨K, hB⟩ := hG.2
  rw [hG.1.cylinder_real_eq_zero]
  exact hB.cylinder_real_pos hw
end IsGibbsMeasure
end BalanceSpecification
