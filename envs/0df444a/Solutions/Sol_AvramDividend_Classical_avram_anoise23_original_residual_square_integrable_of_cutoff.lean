-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise23_original_residual_square_integrable_of_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T09:09:21.963406+00:00
-- url     : https://prove2.me/submissions/1eddd3f1-e7ea-4e5d-b834-2610c2e10f72

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise21_original_gaussian_residual_L2_cutoff_error
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- A physically L²-approximated intrinsic limit inherits square integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ) (t : ℝ≥0)
    (hRsource : ∀ᵐ ω ∂P,
      Tendsto
        (fun n : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (nhds (R t ω)))
    (hRmeas : AEStronglyMeasurable (R t) P)
    (hCutMeas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) P)
    (hCutSquare : Integrable (fun ω =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ^ 2) P) :
    Integrable (fun ω => (R t ω) ^ 2) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let G : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω
  let E : Ω → ℝ := fun ω => R t ω - G ω
  have hErr : Integrable (fun ω => (E ω) ^ 2) P := by
    simpa only [E, G] using
      (avram_anoise21_original_gaussian_residual_L2_cutoff_error
        X hFinite R t hRsource hRmeas hCutMeas 0).1
  have hG : Integrable (fun ω => (G ω) ^ 2) P := by
    simpa only [G] using hCutSquare
  have hDom : Integrable
      (fun ω => 2 * ((E ω) ^ 2 + (G ω) ^ 2)) P := by
    exact (hErr.add hG).const_mul 2
  have hMeas : AEStronglyMeasurable
      (fun ω => (R t ω) ^ 2) P := hRmeas.pow 2
  apply hDom.mono hMeas
  filter_upwards [] with ω
  have hEq : R t ω = E ω + G ω := by dsimp [E]; ring
  have hSq : (R t ω) ^ 2 ≤
      2 * ((E ω) ^ 2 + (G ω) ^ 2) := by
    rw [hEq]
    nlinarith [sq_nonneg (E ω - G ω)]
  have hLeft : 0 ≤ (R t ω) ^ 2 := sq_nonneg _
  have hRight : 0 ≤ 2 * ((E ω) ^ 2 + (G ω) ^ 2) := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hLeft,
    abs_of_nonneg hRight] using hSq