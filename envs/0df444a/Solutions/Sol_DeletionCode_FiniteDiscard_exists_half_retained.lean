-- Prove2me | solution 1 for DeletionCode.FiniteDiscard.exists_half_retained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:07.349939+00:00
-- url     : https://prove2.me/submissions/a4debcd6-01d5-4ea1-b464-f6009c3bc0a1

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Finiteness
import Definitions.Def_DeletionCode_FiniteDiscard
import Theorems.Thm_DeletionCode_FiniteDiscard_exists_half_retained_of_measurable

set_option autoImplicit true
open DeletionCode DeletionCode.FiniteDiscard
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω V : Type*} [MeasurableSpace Ω] [DecidableEq V]
omit [DecidableEq V]
namespace DeletionCode.FiniteDiscard
theorem _root_.solution (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset V) (E : V → Set Ω)
    (hE : ∀ v ∈ s, μ (E v) ≤ ENNReal.ofReal (1 / 3 : ℝ)) :
    ∃ ω, s.card ≤ 2 * (s.filter (fun v => ω ∉ E v)).card := by
  classical
  let T : V → Set Ω := fun v => toMeasurable μ (E v)
  have hT (v : V) (hv : v ∈ s) : μ (T v) ≤ ENNReal.ofReal (1 / 3 : ℝ) := by
    simpa only [T, measure_toMeasurable] using hE v hv
  obtain ⟨ω, hω⟩ := exists_half_retained_of_measurable μ s T
    (fun v _ => measurableSet_toMeasurable μ (E v)) hT
  refine ⟨ω, hω.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))⟩
  intro v hv
  obtain ⟨hvs, hnot⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hvs, fun hmem => hnot ((subset_toMeasurable μ (E v)) hmem)⟩
end DeletionCode.FiniteDiscard
