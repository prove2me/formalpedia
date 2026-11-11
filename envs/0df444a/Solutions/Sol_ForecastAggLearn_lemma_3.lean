-- Prove2me | solution 1 for ForecastAggLearn.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-10T12:27:50.871741+00:00
-- url     : https://prove2.me/submissions/37314f67-5666-4619-b9c7-f60efc08e06a

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.ENNReal.Real

open MeasureTheory
open scoped ENNReal BigOperators

set_option linter.unusedVariables false

private theorem finite_union_bound {X : Type*} [MeasurableSpace X]
    (ν : Measure X) {n : ℕ} (W : Set X) (E : Fin n → Set X) (c : ℝ≥0∞)
    (h : ∀ i, ν (W ∩ E i) ≤ c * ν (E i)) :
    ν (W ∩ ⋃ i, E i) ≤ (n : ℝ≥0∞) * c * ν (⋃ i, E i) := by
  rw [Set.inter_iUnion]
  calc
    ν (⋃ i, W ∩ E i) ≤ ∑' i, ν (W ∩ E i) := measure_iUnion_le _
    _ = ∑ i, ν (W ∩ E i) := tsum_fintype _
    _ ≤ ∑ _i : Fin n, c * ν (⋃ i, E i) := by
      apply Finset.sum_le_sum
      intro i _
      exact (h i).trans (mul_le_mul_right (measure_mono (Set.subset_iUnion E i)) c)
    _ = (n : ℝ≥0∞) * c * ν (⋃ i, E i) := by
      simp [nsmul_eq_mul, mul_assoc]

private theorem measure_bool_partition {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (ω : X → Bool) (hω : Measurable ω) (E : Set X) :
    ν ({x | ω x = true} ∩ E) + ν ({x | ω x = false} ∩ E) = ν E := by
  have htrue : MeasurableSet {x | ω x = true} := hω (measurableSet_singleton true)
  have hfalse : E \ {x | ω x = true} = {x | ω x = false} ∩ E := by
    ext x
    cases h : ω x <;> simp [h]
  rw [Set.inter_comm {x | ω x = true} E, ← hfalse]
  exact measure_inter_add_sdiff E htrue

theorem solution {X : Type*} [mX : MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (ω : X → Bool) (hω : Measurable ω) {n : ℕ} (𝓖 : Fin n → MeasurableSpace X)
    (h𝓖 : ∀ i, 𝓖 i ≤ mX) (F : Fin n → X → ℝ) (hFm : ∀ i, Measurable[𝓖 i] (F i))
    (hF : ∀ i, ∀ E, MeasurableSet[𝓖 i] E →
      ν ({x | ω x = true} ∩ E) = ∫⁻ x in E, ENNReal.ofReal (F i x) ∂ν)
    (α : ℝ) (hα : 0 < α) :
    ν ({x | ω x = false} ∩ {x | ∃ i, 1 - α ≤ F i x}) ≤
      ENNReal.ofReal (n * α) * ν {x | ∃ i, 1 - α ≤ F i x} := by
  let E : Fin n → Set X := fun i => {x | 1 - α ≤ F i x}
  have hweight : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 - α) + ENNReal.ofReal α := by
    simpa only [sub_add_cancel, ENNReal.ofReal_one] using
      (ENNReal.ofReal_add_le (p := 1 - α) (q := α))
  have hbound (i : Fin n) : ν ({x | ω x = false} ∩ E i) ≤ ENNReal.ofReal α * ν (E i) := by
    have hiE : MeasurableSet[𝓖 i] (E i) := by
      let _ : MeasurableSpace X := 𝓖 i
      exact measurableSet_le measurable_const (hFm i)
    have hlower : ENNReal.ofReal (1 - α) * ν (E i) ≤ ν ({x | ω x = true} ∩ E i) := by
      rw [hF i (E i) hiE, ← setLIntegral_const (E i) (ENNReal.ofReal (1 - α))]
      exact setLIntegral_mono' (h𝓖 i _ hiE) (fun _ hx => ENNReal.ofReal_le_ofReal hx)
    apply ENNReal.le_of_add_le_add_left (measure_ne_top ν _)
    calc
      ν ({x | ω x = true} ∩ E i) + ν ({x | ω x = false} ∩ E i) = ν (E i) :=
        measure_bool_partition ν ω hω (E i)
      _ ≤ (ENNReal.ofReal (1 - α) + ENNReal.ofReal α) * ν (E i) := by
        simpa only [one_mul] using mul_le_mul_left hweight (ν (E i))
      _ = ENNReal.ofReal (1 - α) * ν (E i) + ENNReal.ofReal α * ν (E i) := add_mul _ _ _
      _ ≤ ν ({x | ω x = true} ∩ E i) + ENNReal.ofReal α * ν (E i) := add_le_add_left hlower _
  have hE : {x | ∃ i, 1 - α ≤ F i x} = ⋃ i, E i := by
    ext x
    simp [E]
  rw [hE, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  exact finite_union_bound ν _ E _ hbound

#print axioms solution
