-- Prove2me | solution 1 for AvramDividend.Classical.levy_finitePrefix_shifted_increment_rectangle_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:23:22.140804+00:00
-- url     : https://prove2.me/submissions/18b58e94-48d6-4622-8b17-96b5a93b131b

import Mathlib.Probability.IdentDistrib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finitePrefix_increment_rectangle_product

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ)
    (B : Fin n → Set ℝ) (hB : ∀ i, MeasurableSet (B i)) :
    P {ω | (fun i : Fin n =>
      X.X (s + t (i.val + 1)) ω - X.X (s + t i.val) ω) ∈
        Set.pi Set.univ B} =
    P {ω | (fun i : Fin n =>
      X.X (t (i.val + 1)) ω - X.X (t i.val) ω) ∈
        Set.pi Set.univ B} := by
  have h1 := AvramDividend.Classical.levy_finitePrefix_increment_rectangle_product X s
    (fun k => s + t k) (fun a b h => by simp only; gcongr; exact ht h) le_self_add n B hB
  have h2 := AvramDividend.Classical.levy_finitePrefix_increment_rectangle_product X 0
    t ht bot_le n B hB

  rw [h1, h2]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hk : t k ≤ t (k + 1) := ht (Nat.le_succ k)
  have hA : MeasurableSet (if hk : k < n then B ⟨k, hk⟩ else Set.univ) := by
    split_ifs
    · exact hB _
    · exact MeasurableSet.univ
  have e1 := X.stationaryIncrements (s + t k) (s + t (k + 1)) (by gcongr)
  have e2 := X.stationaryIncrements (t k) (t (k + 1)) hk
  rw [add_tsub_add_eq_tsub_left] at e1
  exact (e1.measure_mem_eq hA).trans (e2.measure_mem_eq hA).symm
