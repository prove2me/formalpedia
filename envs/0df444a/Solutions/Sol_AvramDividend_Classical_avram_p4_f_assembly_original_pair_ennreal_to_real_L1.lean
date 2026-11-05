-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_pair_ennreal_to_real_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:42:52.445418+00:00
-- url     : https://prove2.me/submissions/6286e8e4-bd21-4fe0-8570-3b96a7845b60

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Translate a finite original chronological pair ENNReal mean into the real L¹ pair mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let K : Ω → ℝ≥0∞ := fun ω =>
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℕ) : ℝ≥0∞)
    let r : ℝ :=
      (((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
    AEMeasurable K P →
    (∫⁻ ω, K ω ∂P) = ENNReal.ofReal (r ^ 2 / 2) →
    Integrable (fun ω => 2 * (K ω).toReal) P ∧
      (∫ ω, 2 * (K ω).toReal ∂P) = r ^ 2 := by
  classical
  dsimp only
  intro hmeas hmean
  let F : Ω → Finset ℝ≥0 := fun ω =>
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  let K : Ω → ℝ≥0∞ := fun ω =>
    ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℕ) : ℝ≥0∞)
  let r : ℝ := (((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
  change AEMeasurable K P at hmeas
  change (∫⁻ ω, K ω ∂P) = ENNReal.ofReal (r ^ 2 / 2) at hmean
  have hfin : (∫⁻ ω, K ω ∂P) ≠ ⊤ := by
    rw [hmean]
    exact ENNReal.ofReal_ne_top
  have hInt : Integrable (fun ω => (K ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hmeas hfin
  have hKfinite : ∀ᵐ ω ∂P, K ω < ⊤ :=
    Filter.Eventually.of_forall (fun ω => by simp [K])
  have hIntegral : (∫ ω, (K ω).toReal ∂P) = (∫⁻ ω, K ω ∂P).toReal :=
    integral_toReal hmeas hKfinite
  have hReal (ω : Ω) :
      (K ω).toReal =
        (((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℝ) := by
    simp [K]
  constructor
  · exact hInt.const_mul 2
  · calc
      (∫ ω, 2 * (K ω).toReal ∂P) = 2 * (∫ ω, (K ω).toReal ∂P) := by
        rw [integral_const_mul]
      _ = 2 * (ENNReal.ofReal (r ^ 2 / 2)).toReal := by rw [hIntegral, hmean]
      _ = r ^ 2 := by
        rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ r ^ 2 / 2)]
        ring
