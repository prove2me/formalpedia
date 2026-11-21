-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_uniformly_dominated_weighted_smooth_shift_derivative_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:17:47.51997+00:00
-- url     : https://prove2.me/submissions/849bc928-9297-4c1b-9754-ee323fc5ce3c

import Mathlib
open MeasureTheory Filter Set Topology
noncomputable section

theorem solution
    (μ : Measure ℝ) (φ f g : ℝ → ℝ) (ε y : ℝ)
    (hFI : ∀ t, Integrable (fun z => φ z * f (t - ε * z)) μ)
    (hGI : ∀ t, Integrable (fun z => φ z * g (t - ε * z)) μ)
    (hφI : Integrable (fun z => |φ z|) μ)
    (L : ℝ) (hL : 0 ≤ L) (hBd : ∀ t, |g t| ≤ L)
    (hd : ∀ t, HasDerivAt f (g t) t) :
    deriv (fun t => ∫ z, φ z * f (t - ε * z) ∂μ) y =
      ∫ z, φ z * g (y - ε * z) ∂μ := by
  have hs (t z : ℝ) :
      HasDerivAt (fun v : ℝ => v - ε * z) 1 t := by
    simpa using (hasDerivAt_id t).sub_const (ε * z)
  have hmeas : ∀ᶠ t in 𝓝 y,
      AEStronglyMeasurable (fun z => φ z * f (t - ε * z)) μ :=
    Filter.Eventually.of_forall (fun t => (hFI t).aestronglyMeasurable)
  have hb : ∀ᵐ z ∂μ, ∀ t ∈ (Set.univ : Set ℝ),
      ‖φ z * g (t - ε * z)‖ ≤ L * |φ z| := by
    filter_upwards [] with z
    intro t ht
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |φ z| * |g (t - ε * z)| ≤ |φ z| * L :=
        mul_le_mul_of_nonneg_left (hBd _) (abs_nonneg _)
      _ = L * |φ z| := mul_comm _ _
  have hdiff : ∀ᵐ z ∂μ, ∀ t ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun v => φ z * f (v - ε * z))
        (φ z * g (t - ε * z)) t := by
    filter_upwards [] with z
    intro t ht
    simpa only [Function.comp_apply, mul_one] using
      (((hd (t - ε * z)).comp t (hs t z)).const_mul (φ z))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (x₀ := y)
    (F := fun t z => φ z * f (t - ε * z))
    (F' := fun t z => φ z * g (t - ε * z))
    (bound := fun z => L * |φ z|)
    Filter.univ_mem hmeas (hFI y)
    (hGI y).aestronglyMeasurable hb (hφI.const_mul L) hdiff
  exact h.2.deriv
