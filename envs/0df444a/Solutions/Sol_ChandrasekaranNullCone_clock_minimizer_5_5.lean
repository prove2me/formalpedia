-- Prove2me | solution 1 for ChandrasekaranNullCone.clock_minimizer_5_5
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-26T15:33:41.710409+00:00
-- url     : https://prove2.me/submissions/69def741-9563-4033-b6cc-a9080e743793

import Mathlib

open MeasureTheory

namespace ChandrasekaranNullCone.Clock

/-- Pointwise minimization at a fixed clock reading `u ≥ 0`: with `t = L/(L+u)`,
`|t w - w|² + (u/L)|t w|² ≤ |z - w|² + (u/L)|z|²` for every `z`, since the difference is
`(1 + u/L)|z - t w|²`. -/
lemma pointwise_min (L u : ℝ) (hL : 0 < L) (hu : 0 ≤ u) (z w : ℂ) :
    ‖((L / (L + u) : ℝ) : ℂ) * w - w‖ ^ 2 + 1 / L * (u * ‖((L / (L + u) : ℝ) : ℂ) * w‖ ^ 2)
      ≤ ‖z - w‖ ^ 2 + 1 / L * (u * ‖z‖ ^ 2) := by
  have hLu : 0 < L + u := by linarith
  set t : ℝ := L / (L + u) with ht
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero]
  have key : ((z.re - w.re) * (z.re - w.re) + (z.im - w.im) * (z.im - w.im)
      + 1 / L * (u * (z.re * z.re + z.im * z.im)))
      - ((t * w.re - w.re) * (t * w.re - w.re) + (t * w.im - w.im) * (t * w.im - w.im)
      + 1 / L * (u * (t * w.re * (t * w.re) + t * w.im * (t * w.im))))
      = (L + u) / L * ((z.re - t * w.re) ^ 2 + (z.im - t * w.im) ^ 2) := by
    rw [ht]; field_simp; ring
  have hnn : 0 ≤ (L + u) / L * ((z.re - t * w.re) ^ 2 + (z.im - t * w.im) ^ 2) := by positivity
  linarith

end ChandrasekaranNullCone.Clock

open ChandrasekaranNullCone.Clock in
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X) (u : X → ℝ)
    (hu : Measurable u) (hu0 : ∀ x, 0 ≤ u x) (L : ℝ) (hL : 0 < L) (ω ψ : X → ℂ)
    (hω : AEMeasurable ω μ) (hψ : AEMeasurable ψ μ) :
    let ψL : X → ℂ := fun x => ((L / (L + u x) : ℝ) : ℂ) * ω x
    let F : (X → ℂ) → ENNReal := fun φ =>
      (∫⁻ x, ‖φ x - ω x‖ₑ ^ 2 ∂μ) + ENNReal.ofReal (1 / L) * ∫⁻ x, ENNReal.ofReal (u x) * ‖φ x‖ₑ ^ 2 ∂μ
    F ψL ≤ F ψ := by
  intro ψL F
  have hψL : AEMeasurable ψL μ := by
    refine AEMeasurable.mul ?_ hω
    exact (Complex.measurable_ofReal.comp (by fun_prop)).aemeasurable
  have hF : ∀ φ : X → ℂ, AEMeasurable φ μ →
      F φ = ∫⁻ x, ENNReal.ofReal (‖φ x - ω x‖ ^ 2 + 1 / L * (u x * ‖φ x‖ ^ 2)) ∂μ := by
    intro φ hφ
    simp only [F]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left']
    · refine lintegral_congr fun x => ?_
      have hx := hu0 x
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul hx, ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
        ofReal_norm_eq_enorm, ofReal_norm_eq_enorm]
    · exact ((hφ.sub hω).enorm).pow_const 2
  rw [hF ψL hψL, hF ψ hψ]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (pointwise_min L (u x) hL (hu0 x) (ψ x) (ω x))
