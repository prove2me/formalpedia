-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_stopped_diffuse_signed_kernel_integral_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T21:58:13.928199+00:00
-- url     : https://prove2.me/submissions/595afac0-2960-42eb-a709-389d029cdfdf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A jointly strongly measurable version of the original post-source-jump,
pre-dividend-payment gradient remainder has a strongly measurable integral
against any measurable s-finite dividend subkernel. The actual stopping
window retains its closed time horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (_hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0)
    (q : ℝ) (w : ℝ → ℝ)
    (κdiff : Kernel Ω ℝ) [IsSFiniteKernel κdiff]
    (hWindow : ∀ ω : Ω, MeasurableSet
      (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)))
    (hJoint : StronglyMeasurable (fun p : Ω × ℝ =>
      (paymentTimes (σ p.1) ∩ Iic (τ p.1 : ℝ)).indicator
        (fun s : ℝ => Real.exp (-(q * s)) *
          (1 - deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r p.1) s.toNNReal -
            rightLimit D s.toNNReal p.1))) p.2)) :
    StronglyMeasurable (fun ω : Ω =>
      ∫ s in (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω)) ∂κdiff ω) := by
  let g : Ω → ℝ → ℝ := fun ω s => Real.exp (-(q * s)) *
    (1 - deriv w (x +
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
      rightLimit D s.toNNReal ω))
  let f : Ω → ℝ → ℝ := fun ω s =>
    (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)).indicator (g ω) s
  have hf : StronglyMeasurable (Function.uncurry f) := hJoint
  have hm : StronglyMeasurable (fun ω => ∫ s, f ω s ∂κdiff ω) :=
    hf.integral_kernel_prod_right
  have heq : (fun ω => ∫ s, f ω s ∂κdiff ω) =
      (fun ω => ∫ s in (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
        g ω s ∂κdiff ω) := by
    funext ω
    exact integral_indicator (hWindow ω)
  rw [heq] at hm
  exact hm
