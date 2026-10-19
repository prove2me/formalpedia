-- Prove2me | solution 1 for CohnElkies.even_antitone_poisson_convolution_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/b9a75920-5144-4105-9fb0-01955e72fa5c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_even_antitone_poisson_lintegral_max
import Theorems.Thm_CohnElkies_stripPoissonWeightedMeasure_integrable
import Theorems.Thm_CohnElkies_stripPoissonWeightedMeasure_integral

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {f : ℝ → ℝ} {B : ℝ}
    (hf : Integrable f)
    (hfmeas : Measurable f)
    (hfnonneg : ∀ x : ℝ, 0 ≤ f x)
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hanti : AntitoneOn f (Ici (0 : ℝ)))
    (hsupport : Function.support f ⊆ Icc (-B) B)
    (s : ℝ) :
    (∫ x : ℝ, stripPoissonKernel σ (s - x) * f x) ≤
      ∫ x : ℝ, stripPoissonKernel σ (0 - x) * f x := by
  have hsint := stripPoissonWeightedMeasure_integrable
    hbelow habove hf s
  have hzero := stripPoissonWeightedMeasure_integrable
    hbelow habove hf 0
  have hsnonneg :
      0 ≤ᵐ[stripPoissonWeightedMeasure σ s] f :=
    Filter.Eventually.of_forall hfnonneg
  have hzerononneg :
      0 ≤ᵐ[stripPoissonWeightedMeasure σ 0] f :=
    Filter.Eventually.of_forall hfnonneg
  have hlin := even_antitone_poisson_lintegral_max
    hbelow habove hfmeas hfnonneg heven hanti hsupport s
  rw [← ofReal_integral_eq_lintegral_ofReal hsint hsnonneg,
    ← ofReal_integral_eq_lintegral_ofReal hzero hzerononneg] at hlin
  have hcenter :
      0 ≤ ∫ x : ℝ, f x ∂stripPoissonWeightedMeasure σ 0 :=
    integral_nonneg hfnonneg
  have hreal := (ENNReal.ofReal_le_ofReal_iff hcenter).mp hlin
  rw [stripPoissonWeightedMeasure_integral hbelow habove,
    stripPoissonWeightedMeasure_integral hbelow habove] at hreal
  exact hreal
end CohnElkies
