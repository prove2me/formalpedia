-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_kernel_ae_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:42:58.492776+00:00
-- url     : https://prove2.me/submissions/f73bb7af-a68d-46ba-9f87-c18d1c3c790b

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_esscher_laplace_inner_finite
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- The Esscher double-tail kernel is finite almost everywhere in time. -/
theorem solution
    (μ : Measure ℝ) [SFinite μ] (φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 < θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    ∀ᵐ t : ℝ ∂volume,
      (∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
            ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂μ) < ⊤ := by
  let K : ℝ → ℝ → ENNReal := fun t z =>
    if 0 < t ∧ t < z then
      ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
        ENNReal.ofReal (Real.exp (-φ * z))
    else 0
  have hs : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := by
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)
  have hk : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((p.2 - p.1) * Real.exp (-θ * p.1)) *
        ENNReal.ofReal (Real.exp (-φ * p.2))) := by
    fun_prop
  have hf : Measurable (fun p : ℝ × ℝ => K p.1 p.2) := by
    exact hk.ite hs measurable_const
  have hinner : Measurable (fun t : ℝ => ∫⁻ z : ℝ, K t z ∂μ) :=
    hf.lintegral_prod_right
  have hfinite :=
    gaussian_double_tail_esscher_laplace_inner_finite μ φ θ hφ hθ hlevy
  change (∫⁻ t : ℝ, ∫⁻ z : ℝ, K t z ∂μ ∂volume) < ⊤ at hfinite
  change ∀ᵐ t : ℝ ∂volume, (∫⁻ z : ℝ, K t z ∂μ) < ⊤
  exact ae_lt_top hinner (ne_of_lt hfinite)
