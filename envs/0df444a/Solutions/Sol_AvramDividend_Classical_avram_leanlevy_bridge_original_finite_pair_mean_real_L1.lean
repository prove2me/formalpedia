-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_finite_pair_mean_real_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:38:04.330871+00:00
-- url     : https://prove2.me/submissions/9c138db4-58c4-439d-99e2-db155e445092

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (F : Ω → Finset ℝ≥0)
    (hF : ∀ ω, F ω =
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω =
      ((F ω ×ˢ F ω).filter (fun p => p.1 < p.2)).card)
    (hKm : Measurable K)
    (hFinite : (∫⁻ ω, ((2 * K ω : ℕ) : ℝ≥0∞) ∂P) < ⊤) :
    Integrable (fun ω => (2 : ℝ) * (K ω : ℝ)) P ∧
    (∫ ω, (2 : ℝ) * (K ω : ℝ) ∂P) =
      (∫⁻ ω, ((2 * K ω : ℕ) : ℝ≥0∞) ∂P).toReal := by
  have hNonneg : ∀ ω, 0 ≤ (2 : ℝ) * (K ω : ℝ) := by
    intro ω
    positivity
  have hMeas : Measurable (fun ω => (2 : ℝ) * (K ω : ℝ)) := by
    fun_prop
  have hCast (ω : Ω) :
      ENNReal.ofReal ((2 : ℝ) * (K ω : ℝ)) =
        ((2 * K ω : ℕ) : ℝ≥0∞) := by
    norm_cast
  have hEnorm (ω : Ω) :
      ‖(2 : ℝ) * (K ω : ℝ)‖ₑ =
        ((2 * K ω : ℕ) : ℝ≥0∞) := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hNonneg ω)]
    exact hCast ω
  have hFin : HasFiniteIntegral
      (fun ω => (2 : ℝ) * (K ω : ℝ)) P := by
    change (∫⁻ ω, ‖(2 : ℝ) * (K ω : ℝ)‖ₑ ∂P) < ⊤
    simpa only [hEnorm] using hFinite
  have hInt : Integrable (fun ω => (2 : ℝ) * (K ω : ℝ)) P :=
    ⟨hMeas.aestronglyMeasurable, hFin⟩
  refine ⟨hInt, ?_⟩
  have hi :
      (∫ ω, (2 : ℝ) * (K ω : ℝ) ∂P) =
        (∫⁻ ω, ENNReal.ofReal ((2 : ℝ) * (K ω : ℝ)) ∂P).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (μ := P) (f := fun ω => (2 : ℝ) * (K ω : ℝ))
      (Filter.Eventually.of_forall hNonneg) hMeas.aestronglyMeasurable
  have hEq :
      (fun ω : Ω => ENNReal.ofReal ((2 : ℝ) * (K ω : ℝ))) =
        (fun ω : Ω => ((2 * K ω : ℕ) : ℝ≥0∞)) :=
    funext hCast
  rw [hEq] at hi
  exact hi
