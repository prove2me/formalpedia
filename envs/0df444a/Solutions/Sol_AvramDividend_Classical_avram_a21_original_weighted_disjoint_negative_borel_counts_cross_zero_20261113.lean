-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_weighted_disjoint_negative_borel_counts_cross_zero_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:46:26.208266+00:00
-- url     : https://prove2.me/submissions/666ce3ae-a988-4bdb-be6d-f9f55e7dd924

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja33_original_disjoint_negative_borel_cells_cross_zero_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Fixed real weights preserve the original disjoint-mark centred covariance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hNegA : A ⊆ Iio (0 : ℝ)) (hNegB : B ⊆ Iio (0 : ℝ))
    (hDisj : Disjoint A B)
    (a b : ℝ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let rA : ℝ := ((T : ℝ≥0∞) * X.ν A).toReal
    let rB : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    let YA : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ A)).toReal - rA
    let YB : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ B)).toReal - rB
    Integrable (fun ω => (a * YA ω) * (b * YB ω)) P ∧
      (∫ ω, (a * YA ω) * (b * YB ω) ∂P) = 0 := by
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let rA : ℝ := ((T : ℝ≥0∞) * X.ν A).toReal
  let rB : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  let YA : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ A)).toReal - rA
  let YB : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ B)).toReal - rB
  have hCross :=
    avram_ja33_original_disjoint_negative_borel_cells_cross_zero_20261111
      X hFinite T A B hA hB hNegA hNegB hDisj
  change Integrable (fun ω => YA ω * YB ω) P ∧
    (∫ ω, YA ω * YB ω ∂P) = 0 at hCross
  change Integrable (fun ω => (a * YA ω) * (b * YB ω)) P ∧
    (∫ ω, (a * YA ω) * (b * YB ω) ∂P) = 0
  have hWeighted : (fun ω => (a * YA ω) * (b * YB ω)) =
      (fun ω => (a * b) * (YA ω * YB ω)) := by
    funext ω
    ring
  constructor
  · rw [hWeighted]
    exact hCross.1.const_mul (a * b)
  · rw [hWeighted, integral_const_mul, hCross.2, mul_zero]
