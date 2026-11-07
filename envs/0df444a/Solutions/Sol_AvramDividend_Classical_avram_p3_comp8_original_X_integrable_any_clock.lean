-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp8_original_X_integrable_any_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:56:49.698409+00:00
-- url     : https://prove2.me/submissions/6b9ffa3d-b7ea-40dd-b923-09d13114f1a7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_X_integrable_mean_additivity
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (t : ℝ≥0) :
    Integrable (X.X t) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hNat : ∀ n : ℕ, Integrable (X.X (n : ℝ≥0)) P := by
    intro n
    induction n with
    | zero =>
        convert (integrable_const (0 : ℝ) :
          Integrable (fun _ : Ω => (0 : ℝ)) P) using 1
        funext ω
        simp [X.X_zero]
    | succ n ih =>
        have hSucc :=
          (avram_wave7_06_original_X_integrable_mean_additivity
            X (n : ℝ≥0) 1 ih hX.2.1).1
        simpa only [Nat.cast_succ] using hSucc
  obtain ⟨N, hN⟩ := exists_nat_gt (t : ℝ)
  have htN : t ≤ (N : ℝ≥0) := by
    exact_mod_cast (le_of_lt hN)
  have hNR : Integrable
      (fun ω => (N : ℝ) * X.drift - X.X (N : ℝ≥0) ω) P :=
    (integrable_const _).sub (hNat N)
  have hMeas : Measurable
      (fun ω : Ω => (t : ℝ) * X.drift - X.X t ω) :=
    measurable_const.sub ((X.adapted t).mono (𝓕.le _) le_rfl)
  have hDom : ∀ᵐ ω ∂P,
      ‖(t : ℝ) * X.drift - X.X t ω‖ ≤
        (N : ℝ) * X.drift - X.X (N : ℝ≥0) ω := by
    filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
      with ω hm
    have h0 := hm (show (0 : ℝ≥0) ≤ t from bot_le)
    have h1 := hm htN
    have hr0 : 0 ≤ (t : ℝ) * X.drift - X.X t ω := by
      simpa [X.X_zero] using h0
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact h1
  have hResidual : Integrable
      (fun ω => (t : ℝ) * X.drift - X.X t ω) P :=
    hNR.mono' hMeas.aestronglyMeasurable hDom
  have hDifference := (integrable_const ((t : ℝ) * X.drift)).sub hResidual
  convert hDifference using 1
  funext ω
  change X.X t ω =
    (t : ℝ) * X.drift - ((t : ℝ) * X.drift - X.X t ω)
  ring
