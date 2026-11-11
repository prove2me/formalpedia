-- Prove2me | solution 1 for ForecastAggLearn.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-10T12:25:20.290418+00:00
-- url     : https://prove2.me/submissions/ba1651a0-e0a2-46ef-9a76-623caa85248b

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

theorem solution {X : Type*} [mX : MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (ω : X → Bool) (hω : Measurable ω) {n : ℕ} (𝓖 : Fin n → MeasurableSpace X)
    (h𝓖 : ∀ i, 𝓖 i ≤ mX) (F : Fin n → X → ℝ) (hFm : ∀ i, Measurable[𝓖 i] (F i))
    (hF : ∀ i, ∀ E, MeasurableSet[𝓖 i] E →
      ν ({x | ω x = true} ∩ E) = ∫⁻ x in E, ENNReal.ofReal (F i x) ∂ν)
    (α : ℝ) (hα : 0 < α) :
    ν ({x | ω x = true} ∩ {x | ∃ i, F i x ≤ α}) ≤
      ENNReal.ofReal (n * α) * ν {x | ∃ i, F i x ≤ α} := by
  let E : Fin n → Set X := fun i => {x | F i x ≤ α}
  have hbound (i : Fin n) : ν ({x | ω x = true} ∩ E i) ≤ ENNReal.ofReal α * ν (E i) := by
    have hiE : MeasurableSet[𝓖 i] (E i) := by
      let _ : MeasurableSpace X := 𝓖 i
      exact measurableSet_le (hFm i) measurable_const
    rw [hF i (E i) hiE, ← setLIntegral_const (E i) (ENNReal.ofReal α)]
    exact setLIntegral_mono' (h𝓖 i _ hiE) (fun _ hx => ENNReal.ofReal_le_ofReal hx)
  have hE : {x | ∃ i, F i x ≤ α} = ⋃ i, E i := by
    ext x
    simp [E]
  rw [hE, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  exact finite_union_bound ν _ E _ hbound

#print axioms solution
