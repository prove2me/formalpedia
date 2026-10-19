-- Prove2me | solution 1 for CohnElkies.stripRegularizedOuter_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/606b9cd2-6b98-4175-b7dc-a5678894b400

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripRegularizedHolomorphicPoissonKernel_re
import Theorems.Thm_CohnElkies_stripPoisson_integral_changeVariables

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ σ : ℝ} (hℓ : 0 < ℓ)
    (hσbelow : -1 < σ) (hσabove : σ < 1)
    (s : ℝ) (b : ℝ → ℝ)
    (houter : Integrable
      (fun y : ℝ =>
        stripRegularizedHolomorphicPoissonKernel ℓ
            ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y *
          (b y : ℂ))) :
    (stripRegularizedOuter ℓ b
      ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ))).re =
      ∫ T : ℝ, stripPoissonKernel σ T * b (s - ℓ * T) := by
  unfold stripRegularizedOuter
  calc
    (∫ y : ℝ,
        stripRegularizedHolomorphicPoissonKernel ℓ
            ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y *
          (b y : ℂ)).re =
      ∫ y : ℝ,
        (stripRegularizedHolomorphicPoissonKernel ℓ
            ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y *
          (b y : ℂ)).re := by
      exact (integral_re houter).symm
    _ =
      ∫ y : ℝ,
        stripPoissonKernel σ ((s - y) / ℓ) / ℓ * b y := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun y => ?_)
      change
        (stripRegularizedHolomorphicPoissonKernel ℓ
            ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y *
          (b y : ℂ)).re =
          stripPoissonKernel σ ((s - y) / ℓ) / ℓ * b y
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero,
        stripRegularizedHolomorphicPoissonKernel_re
          hℓ hσbelow hσabove]
    _ = ∫ T : ℝ, stripPoissonKernel σ T * b (s - ℓ * T) :=
      stripPoisson_integral_changeVariables hℓ σ s b
end CohnElkies
