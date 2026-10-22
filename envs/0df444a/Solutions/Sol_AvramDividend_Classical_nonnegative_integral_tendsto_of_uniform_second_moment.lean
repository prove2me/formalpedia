-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_integral_tendsto_of_uniform_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:28:53.167382+00:00
-- url     : https://prove2.me/submissions/cf487204-2942-409b-a379-38d544c193c5

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Theorems.Thm_AvramDividend_Classical_chat03_integrable_of_quadratic_lintegral_bound
import Theorems.Thm_AvramDividend_Classical_chat03_ae_limit_quadratic_moment_bound
import Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_ae_limit
import Theorems.Thm_AvramDividend_Classical_chat03_ae_limit_real_quadratic_moment_bound
import Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_truncation_integral_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_uniform_quadratic_truncation_approximation
import Theorems.Thm_AvramDividend_Classical_chat03_tendsto_of_uniform_truncation_approximations

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal

/-!
Uniform quadratic bounds imply convergence of the exact real
expectations by combining finite clipping, uniform approximation,
and the Fatou bound for the limit's real quadratic moment.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hYm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hY0 : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Y n ω)
    (hZ : AEStronglyMeasurable Z P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω)))
    (C : ℝ) (hC : 0 ≤ C)
    (hY2 : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) P ∧
      ∫ ω, (Y n ω) ^ 2 ∂P ≤ C) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (𝓝 (∫ ω, Z ω ∂P)) := by
  have hlin := chat03_ae_limit_quadratic_moment_bound
    P Y Z C hYm hconv hY2
  have hZi := chat03_integrable_of_quadratic_lintegral_bound
    Z hZ C hlin
  have hZ0 := chat03_nonnegative_ae_limit P Y Z hY0 hconv
  have hZ2 := chat03_ae_limit_real_quadratic_moment_bound
    Y Z hYm hZ hconv C hC hY2
  refine ⟨hZi, ?_⟩
  apply chat03_tendsto_of_uniform_truncation_approximations
    (fun n => ∫ ω, Y n ω ∂P)
    (fun R n => ∫ ω, min (Y n ω) R ∂P)
    (∫ ω, Z ω ∂P)
    (fun R => ∫ ω, min (Z ω) R ∂P)
  · intro R hR
    exact chat03_nonnegative_truncation_integral_tendsto
      Y Z R (le_of_lt hR) hYm hY0 hconv
  · exact chat03_uniform_quadratic_truncation_approximation
      Y Z hYm hY0 hZ hZ0 C hC hY2 hZ2
