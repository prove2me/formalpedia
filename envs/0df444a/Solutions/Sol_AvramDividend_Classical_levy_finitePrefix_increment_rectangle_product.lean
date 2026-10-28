-- Prove2me | solution 1 for AvramDividend.Classical.levy_finitePrefix_increment_rectangle_product
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:15:15.526458+00:00
-- url     : https://prove2.me/submissions/ca4cbe28-ea8f-49e0-ba95-4ee26f76e852

import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_all_finite_prefix_increment_cylinder_product

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (t : ℕ → ℝ≥0) (ht : Monotone t) (hst : s ≤ t 0)
    (n : ℕ) (B : Fin n → Set ℝ) (hB : ∀ i, MeasurableSet (B i)) :
    P {ω | (fun i : Fin n =>
      X.X (t (i.val + 1)) ω - X.X (t i.val) ω) ∈ Set.pi Set.univ B} =
      ∏ k ∈ Finset.range n,
        P {ω | X.X (t (k + 1)) ω - X.X (t k) ω ∈
          (if hk : k < n then B ⟨k, hk⟩ else Set.univ)} := by
  haveI := X.isProbability
  have h := AvramDividend.Classical.chat04_all_finite_prefix_increment_cylinder_product X s
    Set.univ MeasurableSet.univ t ht hst
    (fun k => if hk : k < n then B ⟨k, hk⟩ else Set.univ)
    (fun k => by by_cases hk : k < n <;> simp [hk, hB]) n
  rw [measure_univ, one_mul, Set.univ_inter] at h
  rw [← h]
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro hω i hi
    simpa [hi] using hω ⟨i, hi⟩
  · intro hω i
    simpa [i.isLt] using hω i.val i.isLt
