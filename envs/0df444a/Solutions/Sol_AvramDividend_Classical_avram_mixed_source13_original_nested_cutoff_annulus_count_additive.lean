-- Prove2me | solution 1 for AvramDividend.Classical.avram_mixed_source13_original_nested_cutoff_annulus_count_additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:22:15.461435+00:00
-- url     : https://prove2.me/submissions/2650389f-bda0-4459-880b-ac77f91bad39

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_disjoint_mark_band_union_additive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- The actual path's nested cutoff counts partition at their disjoint annulus. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) (ω : Ω) :
    let c : ℝ := -(1 / ((n : ℝ) + 1))
    let d : ℝ := -(1 / ((m : ℝ) + 1))
    let J : Set ℝ → ℝ≥0∞ := fun B =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    J (Iic d) = J (Iic c) + J (Ioc c d) := by
  classical
  let c : ℝ := -(1 / ((n : ℝ) + 1))
  let d : ℝ := -(1 / ((m : ℝ) + 1))
  let J : Set ℝ → ℝ≥0∞ := fun B =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  change J (Iic d) = J (Iic c) + J (Ioc c d)
  have hcd : c ≤ d := by
    dsimp [c, d]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hnmR : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      have hNat : n + 1 ≤ m + 1 := by omega
      exact_mod_cast hNat
    have hrec : (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le hn hnmR
    linarith
  have hdis : Disjoint (Iic c) (Ioc c d) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hx) hy.1
  have hunion : Iic d = Iic c ∪ Ioc c d := by
    ext x
    simp only [Set.mem_Iic, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro hx
      by_cases hxc : x ≤ c
      · exact Or.inl hxc
      · exact Or.inr ⟨lt_of_not_ge hxc, hx⟩
    · intro hMem
      rcases hMem with hLeft | hRight
      · exact le_trans hLeft hcd
      · exact hRight.2
  have hadd :=
    avram_p4_b_smalljump_original_intrinsic_disjoint_mark_band_union_additive
      X 0 T (Iic c) (Ioc c d) measurableSet_Iic measurableSet_Ioc hdis ω
  change J (Iic c ∪ Ioc c d) = J (Iic c) + J (Ioc c d) at hadd
  rw [← hunion] at hadd
  exact hadd
