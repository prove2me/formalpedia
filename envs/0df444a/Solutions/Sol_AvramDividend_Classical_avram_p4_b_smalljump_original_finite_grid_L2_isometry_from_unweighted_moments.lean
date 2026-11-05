-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_finite_grid_L2_isometry_from_unweighted_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:56:33.828072+00:00
-- url     : https://prove2.me/submissions/f50f8990-103e-46bb-b4ac-691d90564a87

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_grid_L2_isometry

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original finite-grid L² isometry from unweighted physical
diagonal moments and pairwise compensated orthogonality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (B : ι → Set ℝ) (J : ι → Ω → ℝ)
    (hSource : ∀ i ∈ S, ∀ ω, J i ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B i)).toReal)
    (r c : ι → ℝ)
    (hRate : ∀ i ∈ S, r i =
      ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i))).toReal)
    (hPairInt : ∀ i ∈ S, ∀ j ∈ S, Integrable (fun ω =>
      (c i * (J i ω - r i)) * (c j * (J j ω - r j))) P)
    (hVar : ∀ i ∈ S,
      (∫ ω, (J i ω - r i) ^ 2 ∂P) = r i)
    (hOrth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (∫ ω, (J i ω - r i) * (J j ω - r j) ∂P) = 0) :
    (∫ ω, (∑ i ∈ S, c i * (J i ω - r i)) ^ 2 ∂P) =
      ∑ i ∈ S, c i ^ 2 * r i := by
  have hPair (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      (∫ ω, (c i * (J i ω - r i)) *
        (c j * (J j ω - r j)) ∂P) =
          if i = j then c i ^ 2 * r i else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [if_pos rfl]
      calc
        _ = ∫ ω, c i ^ 2 * (J i ω - r i) ^ 2 ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          ring
        _ = c i ^ 2 * r i := by rw [integral_const_mul, hVar i hi]
    · simp only [if_neg hij]
      calc
        _ = ∫ ω, (c i * c j) *
          ((J i ω - r i) * (J j ω - r j)) ∂P := by
            apply integral_congr_ae
            filter_upwards [] with ω
            ring
        _ = 0 := by rw [integral_const_mul, hOrth i hi j hj hij]; ring
  exact avram_p4_b_smalljump_original_finite_grid_L2_isometry
    X s t S B J hSource r c hRate hPairInt hPair
