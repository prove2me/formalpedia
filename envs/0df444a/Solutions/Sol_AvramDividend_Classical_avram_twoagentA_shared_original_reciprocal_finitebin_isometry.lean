-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_shared_original_reciprocal_finitebin_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:40:51.211188+00:00
-- url     : https://prove2.me/submissions/d2ac8ecd-7f49-4f7d-89af-a8cf269624e1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf17_ordered_finite_physical_mark_isometry
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n m : ℕ) :
    let S : Finset ℕ := Finset.Ico n m
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      NX ω (Ioc 0 T ×ˢ B i)
    let r : ℕ → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let c : ℕ → ℝ := fun i => -(1 / ((i : ℝ) + 1))
    (∫ ω, (∑ i ∈ S, c i * ((N i ω).toReal - r i)) ^ 2 ∂P) =
      ∑ i ∈ S, c i ^ 2 * r i := by
  classical
  let S : Finset ℕ := Finset.Ico n m
  have hLe :
      ∀ i ∈ S, (fun j : ℕ => j) i ≤ (fun j : ℕ => j + 1) i := by
    intro i hi
    exact Nat.le_succ i
  have hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (fun k : ℕ => k + 1) i ≤ (fun k : ℕ => k) j ∨
      (fun k : ℕ => k + 1) j ≤ (fun k : ℕ => k) i := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact Or.inl (Nat.succ_le_of_lt hlt)
    · exact Or.inr (Nat.succ_le_of_lt hgt)
  simpa [S, Nat.cast_add, add_assoc, one_add_one_eq_two] using
    (avram_mix_inf17_ordered_finite_physical_mark_isometry
      X T S (fun i => i) (fun i => i + 1) hLe hSep
      (fun i => -(1 / ((i : ℝ) + 1))))
