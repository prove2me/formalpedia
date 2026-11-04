-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_joint_mark_weight_iSup_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:38:13.83691+00:00
-- url     : https://prove2.me/submissions/d47d32c1-1427-4226-b090-8b6df10901c1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_monotone_mark_pathwise
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_ennreal_diagonal_iSup_mul

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Simultaneous monotone convergence in a genuine Lévy mark band and
its extended-real path weight; no rate fact and no finiteness is assumed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : ℕ → Set ℝ)
    (hB : ∀ n, MeasurableSet (B n))
    (hBMono : Monotone B)
    (H : ℕ → Ω → ℝ≥0∞)
    (hH : ∀ n, Measurable (H n))
    (hHMono : ∀ i j, i ≤ j → ∀ ω, H i ω ≤ H j ω) :
    (∫⁻ ω, (⨆ n, H n ω) * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (⋃ n, B n)) ∂P) =
    ⨆ n, (∫⁻ ω, H n ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B n)) ∂P) := by
  let N : Set ℝ → Ω → ℝ≥0∞ := fun D ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ D)
  have hPath : ∀ ω, N (⋃ n, B n) ω = ⨆ n, N (B n) ω :=
    avram_p2_f_weighted_original_monotone_mark_pathwise X s T B hBMono
  have hNMono : ∀ ω, Monotone (fun n : ℕ => N (B n) ω) := by
    intro ω i j hij
    exact measure_mono (Set.prod_mono Subset.rfl (hBMono hij))
  have hMeas (n : ℕ) :
      Measurable (fun ω => H n ω * N (B n) ω) := by
    exact (hH n).mul
      (avram_p2_f_weighted_original_intrinsic_rectangle_measurable
        X s T (B n) (hB n))
  have hMonoProd : Monotone
      (fun n : ℕ => fun ω => H n ω * N (B n) ω) := by
    intro i j hij ω
    calc
      H i ω * N (B i) ω ≤ H j ω * N (B i) ω :=
        mul_le_mul_of_nonneg_right (hHMono i j hij ω) zero_le
      _ ≤ H j ω * N (B j) ω :=
        mul_le_mul_of_nonneg_left
          (measure_mono (Set.prod_mono Subset.rfl (hBMono hij))) zero_le
  change (∫⁻ ω, (⨆ n, H n ω) * N (⋃ n, B n) ω ∂P) =
    ⨆ n, (∫⁻ ω, H n ω * N (B n) ω ∂P)
  calc
    (∫⁻ ω, (⨆ n, H n ω) * N (⋃ n, B n) ω ∂P) =
      (∫⁻ ω, ⨆ n, H n ω * N (B n) ω ∂P) := by
        congr 1
        funext ω
        rw [hPath ω]
        exact avram_p2_f_weighted_ennreal_diagonal_iSup_mul
          (fun n => H n ω) (fun n => N (B n) ω)
          (by intro i j hij; exact hHMono i j hij ω) (hNMono ω)
    _ = _ := MeasureTheory.lintegral_iSup hMeas hMonoProd
