-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_signed_gaussian_positive_l1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:55:46.790279+00:00
-- url     : https://prove2.me/submissions/9fc44886-40b5-4cbb-b111-b806cbd391a2

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Theorems.Thm_AvramDividend_Classical_nonnegative_integrable_tsum_of_summable_integrals
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Gaussian signed Neumann powers are L1 with bounds only on the positive axis. -/
theorem solution
    (P F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hFL1 : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ F n x)
    (hDom : ∀ n : ℕ, ∀ x : ℝ, 0 < x → |P n x| ≤ F n x)
    (hFbound : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (hFmass : Summable (fun n : ℕ =>
      ∫ x in Ioi (0 : ℝ), F n x ∂volume)) :
    IntegrableOn (fun x : ℝ => ∑' n : ℕ, P n x)
      (Ioi (0 : ℝ)) volume := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let E : ℕ → ℝ → ℝ := fun n x => if 0 < x then F n x else 0
  have hEpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ E n x := by
    intro n x
    by_cases hx : 0 < x
    · simp only [E, if_pos hx]
      exact hFpos n x hx
    · simp only [E, if_neg hx, le_refl]
  have hFsum (x : ℝ) (hx : 0 < x) :
      Summable (fun n : ℕ => F n x) :=
    renewal_density_series_summable_of_geometric_power_bound
      ρ x hρ0 hρ1 hx (fun n => F n x)
      (fun n => hFpos n x hx) (fun n => hFbound n x hx)
  have hEsum : ∀ x : ℝ, Summable (fun n : ℕ => E n x) := by
    intro x
    by_cases hx : 0 < x
    · simpa only [E, if_pos hx] using hFsum x hx
    · simp only [E, if_neg hx]
      exact summable_zero
  have hEae (n : ℕ) : E n =ᵐ[μ] F n := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : 0 < x := hx
    simp only [E, if_pos hx']
  have hEL1 : ∀ n : ℕ, Integrable (E n) μ := by
    intro n
    exact (hFL1 n).congr (hEae n).symm
  have hEmass : Summable (fun n : ℕ =>
      ∫ x : ℝ, E n x ∂μ) := by
    have hEq : (fun n : ℕ => ∫ x : ℝ, E n x ∂μ) =
        (fun n : ℕ => ∫ x : ℝ, F n x ∂μ) := by
      funext n
      exact integral_congr_ae (hEae n)
    rw [hEq]
    exact hFmass
  have hG : Integrable (fun x : ℝ => ∑' n : ℕ, E n x) μ :=
    nonnegative_integrable_tsum_of_summable_integrals
      μ E hEL1 hEpos hEsum hEmass
  have hPmeas : AEStronglyMeasurable
      (fun x : ℝ => ∑' n : ℕ, P n x) μ :=
    (AEMeasurable.tsum (fun n => (hPL1 n).aemeasurable)).aestronglyMeasurable
  have hPG : ∀ᵐ x ∂μ,
      ‖∑' n : ℕ, P n x‖ ≤ ∑' n : ℕ, E n x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : 0 < x := hx
    have hb := tsum_of_norm_bounded (f := fun n : ℕ => P n x)
      (hFsum x hx').hasSum
      (fun n => by simpa only [Real.norm_eq_abs] using hDom n x hx')
    simpa only [E, if_pos hx'] using hb
  exact Integrable.mono' hG hPmeas hPG
