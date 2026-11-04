-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_joint_horizon_mark_weight_iSup_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:53:11.927343+00:00
-- url     : https://prove2.me/submissions/d421fda8-e189-4dd5-a2d5-13286e829449

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_ennreal_diagonal_iSup_mul
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_joint_horizon_mark_iSup_pathwise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Triple monotone convergence for actual original Lévy future jump rectangles.
No ν-rate, finiteness or adaptedness premise is needed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (T : ℕ → ℝ≥0) (hT : Monotone T)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hBMono : Monotone B)
    (H : ℕ → Ω → ℝ≥0∞)
    (hH : ∀ n, Measurable (H n))
    (hHMono : ∀ i j, i ≤ j → ∀ ω, H i ω ≤ H j ω) :
    (∫⁻ ω, (⨆ n, H n ω) * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (⋃ n, Ioc s (s + T n) ×ˢ B n) ∂P) =
    ⨆ n, (∫⁻ ω, H n ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T n) ×ˢ B n) ∂P) := by
  let N : Set (ℝ≥0 × ℝ) → Ω → ℝ≥0∞ := fun D ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) D
  let S : ℕ → Set (ℝ≥0 × ℝ) :=
    fun n => Ioc s (s + T n) ×ˢ B n
  have hSets : Monotone S := by
    intro i j hij
    apply Set.prod_mono
    · intro u hu
      have hTime : s + T i ≤ s + T j := by
        simpa only [add_comm] using (add_le_add_left (hT hij) s)
      exact ⟨hu.1, le_trans hu.2 hTime⟩
    · exact hBMono hij
  have hPath : ∀ ω, N (⋃ n, S n) ω = ⨆ n, N (S n) ω := by
    intro ω
    exact avram_p2_f_weighted_original_joint_horizon_mark_iSup_pathwise
      X s T hT B hBMono ω
  have hNMono : ∀ ω, Monotone (fun n : ℕ => N (S n) ω) := by
    intro ω i j hij
    exact measure_mono (hSets hij)
  have hMeas (n : ℕ) :
      Measurable (fun ω => H n ω * N (S n) ω) := by
    exact (hH n).mul
      (avram_p2_f_weighted_original_intrinsic_rectangle_measurable
        X s (T n) (B n) (hB n))
  have hMonoProd : Monotone
      (fun n : ℕ => fun ω => H n ω * N (S n) ω) := by
    intro i j hij ω
    calc
      H i ω * N (S i) ω ≤ H j ω * N (S i) ω :=
        mul_le_mul_of_nonneg_right (hHMono i j hij ω) zero_le
      _ ≤ H j ω * N (S j) ω :=
        mul_le_mul_of_nonneg_left (measure_mono (hSets hij)) zero_le
  change (∫⁻ ω, (⨆ n, H n ω) * N (⋃ n, S n) ω ∂P) =
    ⨆ n, (∫⁻ ω, H n ω * N (S n) ω ∂P)
  calc
    (∫⁻ ω, (⨆ n, H n ω) * N (⋃ n, S n) ω ∂P) =
      (∫⁻ ω, ⨆ n, H n ω * N (S n) ω ∂P) := by
        congr 1
        funext ω
        rw [hPath ω]
        exact avram_p2_f_weighted_ennreal_diagonal_iSup_mul
          (fun n => H n ω) (fun n => N (S n) ω)
          (by intro i j hij; exact hHMono i j hij ω) (hNMono ω)
    _ = _ := MeasureTheory.lintegral_iSup hMeas hMonoProd
