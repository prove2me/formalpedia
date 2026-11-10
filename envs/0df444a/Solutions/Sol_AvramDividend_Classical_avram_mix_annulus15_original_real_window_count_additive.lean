-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_annulus15_original_real_window_count_additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T17:48:16.545147+00:00
-- url     : https://prove2.me/submissions/d075df33-b146-434f-ba7b-dde09e4d76a8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_disjoint_mark_band_union_additive
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_window_count_finset_filter
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus14_original_window_filter_card
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Original physical real counts split over two nested negative mark cutoffs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ≥0) (hst : s ≤ t) (n m : ℕ) (hnm : n ≤ m) :
    let c : ℝ := -(1 / ((n : ℝ) + 1))
    let d : ℝ := -(1 / ((m : ℝ) + 1))
    let J : Set ℝ → ℝ≥0∞ := fun B =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    (J (Iic d)).toReal =
      (J (Iic c)).toReal + (J (Ioc c d)).toReal := by
  classical
  let c : ℝ := -(1 / ((n : ℝ) + 1))
  let d : ℝ := -(1 / ((m : ℝ) + 1))
  let J : Set ℝ → ℝ≥0∞ := fun B =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B)
  change (J (Iic d)).toReal =
    (J (Iic c)).toReal + (J (Ioc c d)).toReal
  have hcd : c ≤ d := by
    dsimp [c, d]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hnmR : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    exact neg_le_neg (one_div_le_one_div_of_le hn hnmR)
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
      X s t (Iic c) (Ioc c d) measurableSet_Iic measurableSet_Ioc hdis ω
  change J (Iic c ∪ Ioc c d) = J (Iic c) + J (Ioc c d) at hadd
  rw [← hunion] at hadd
  have hfinA : J (Iic c) ≠ ⊤ := by
    have h := avram_p2_e_compensator_original_window_count_finset_filter
      X ω s t t hst le_rfl n
    change J (Iic c) = _ at h
    rw [h]; simp
  have hfinB : J (Ioc c d) ≠ ⊤ := by
    have h := avram_mix_annulus14_original_window_filter_card
      X ω s t t hst le_rfl n m hnm
    change J (Ioc c d) = _ at h
    rw [h]; simp
  calc
    (J (Iic d)).toReal =
        (J (Iic c) + J (Ioc c d)).toReal :=
      congrArg ENNReal.toReal hadd
    _ = _ := ENNReal.toReal_add hfinA hfinB
