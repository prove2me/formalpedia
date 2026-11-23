-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_nonnegative_real_to_ennreal_mean_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:53:49.034196+00:00
-- url     : https://prove2.me/submissions/f7aa0e26-717d-4332-9d69-3f398a246c91

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal

/-! An integrable nonnegative Bochner mean limit is the genuine ENNReal lintegral mean limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hY : ∀ n, Integrable (Y n) P) (hZ : Integrable Z P)
    (hYn : ∀ n, 0 ≤ᵐ[P] Y n) (hZn : 0 ≤ᵐ[P] Z)
    (hMean : Tendsto (fun n : ℕ => ∫ ω, Y n ω ∂P)
      atTop (nhds (∫ ω, Z ω ∂P))) :
    Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (Y n ω) ∂P)
      atTop (nhds (∫⁻ ω, ENNReal.ofReal (Z ω) ∂P)) := by
  have hYeq (n : ℕ) :
      (∫⁻ ω, ENNReal.ofReal (Y n ω) ∂P) =
        ENNReal.ofReal (∫ ω, Y n ω ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal (hY n) (hYn n)).symm
  have hZeq :
      (∫⁻ ω, ENNReal.ofReal (Z ω) ∂P) =
        ENNReal.ofReal (∫ ω, Z ω ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hZ hZn).symm
  have hENN := (ENNReal.continuous_ofReal.tendsto _).comp hMean
  simpa only [hYeq, hZeq, Function.comp_def] using hENN
