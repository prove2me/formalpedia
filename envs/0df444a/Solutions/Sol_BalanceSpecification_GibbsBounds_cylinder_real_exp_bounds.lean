-- Prove2me | solution 1 for BalanceSpecification.GibbsBounds.cylinder_real_exp_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:39.494057+00:00
-- url     : https://prove2.me/submissions/be545f30-4a7d-4273-8c3f-63b430faabe0

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
theorem _root_.solution {X : ShiftSpace A}
    {hX : X.carrier.Nonempty} {μ : ProbabilityMeasure X.carrier} {K : ℝ}
    (hB : GibbsBounds hX μ K) {w : Word A} (hw : w ∈ language X) :
    Real.exp (-((w.length : ℝ) * entropy X hX)) / K ≤
        (μ : Measure X.carrier).real (cylinder X w 0) ∧
    (μ : Measure X.carrier).real (cylinder X w 0) ≤
      K * Real.exp (-((w.length : ℝ) * entropy X hX)) := by
  let t := (w.length : ℝ) * entropy X hX
  have hexp : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  obtain ⟨hl, hu⟩ := hB.2 w hw
  constructor
  · calc
      Real.exp (-t) / K = (1 / K) * Real.exp (-t) := by ring
      _ ≤ ((μ : Measure X.carrier).real (cylinder X w 0) * Real.exp t) *
          Real.exp (-t) := mul_le_mul_of_nonneg_right hl (Real.exp_nonneg _)
      _ = (μ : Measure X.carrier).real (cylinder X w 0) := by
        rw [mul_assoc, hexp, mul_one]
  · calc
      (μ : Measure X.carrier).real (cylinder X w 0) =
          ((μ : Measure X.carrier).real (cylinder X w 0) * Real.exp t) *
            Real.exp (-t) := by rw [mul_assoc, hexp, mul_one]
      _ ≤ K * Real.exp (-t) := mul_le_mul_of_nonneg_right hu (Real.exp_nonneg _)
end GibbsBounds
end BalanceSpecification
