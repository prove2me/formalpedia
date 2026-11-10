-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_annulus16_original_bounded_random_weighted_count_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:09:38.766343+00:00
-- url     : https://prove2.me/submissions/eaa61ac1-b440-44a7-b42c-9ae943a5d163

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus16_original_constant_weighted_count_variance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m)
    (H : Ω → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hBound : ∀ ω, |H ω| ≤ L) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    AEStronglyMeasurable
        (fun ω => (H ω * ((N ω).toReal - r)) ^ 2) P →
      Integrable (fun ω => (H ω * ((N ω).toReal - r)) ^ 2) P ∧
      (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) ≤ L ^ 2 * r := by
  dsimp only
  intro hMeas
  let B : Set ℝ :=
    Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  have hbase :=
    avram_mix_annulus16_original_constant_weighted_count_variance
      X T n m hnm L
  rcases hbase with ⟨hI, hEq⟩
  have hsq (ω : Ω) : (H ω) ^ 2 ≤ L ^ 2 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hBound ω)
    have hr : 0 ≤ L - H ω := sub_nonneg.mpr hhi
    have hl : 0 ≤ L + H ω := by linarith
    nlinarith [mul_nonneg hr hl]
  have hpoint (ω : Ω) :
      (H ω * ((N ω).toReal - r)) ^ 2 ≤
        (L * ((N ω).toReal - r)) ^ 2 := by
    have hpos := sq_nonneg ((N ω).toReal - r)
    have hh := mul_nonneg (sub_nonneg.mpr (hsq ω)) hpos
    nlinarith [hh]
  have hdom (ω : Ω) :
      ‖(H ω * ((N ω).toReal - r)) ^ 2‖ ≤
        (L * ((N ω).toReal - r)) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint ω
  have hWeightedI :
      Integrable (fun ω => (H ω * ((N ω).toReal - r)) ^ 2) P :=
    hI.mono' hMeas (Filter.Eventually.of_forall hdom)
  refine ⟨hWeightedI, ?_⟩
  calc
    (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P)
        ≤ ∫ ω, (L * ((N ω).toReal - r)) ^ 2 ∂P := by
            exact integral_mono hWeightedI hI hpoint
    _ = L ^ 2 * r := hEq
