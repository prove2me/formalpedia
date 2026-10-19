-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_mul_lowerRiemannLog_zero_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/99e91059-b7af-4259-9b5c-6e29c51d51e5

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_neg
import Theorems.Thm_CohnElkies_stripPoissonKernel_integrable
import Theorems.Thm_CohnElkies_lowerGammaScaled_poisson_product_integrable
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_integer_scaled

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
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable (fun T : ℝ =>
      stripPoissonKernel σ T * lowerRiemannLog T 0) := by
  have hgamma0 := lowerGammaScaled_poisson_product_integrable
    (d := 2) (by norm_num : 0 < (2 : ℕ))
    (R := (1 : ℝ)) hbelow habove 0
  have hgamma : Integrable (fun T : ℝ =>
      stripPoissonKernel σ T * lowerGammaBoundaryLog 1 1 T) := by
    apply hgamma0.congr
    filter_upwards [] with T
    norm_num [stripPoissonKernel_neg]
  have hk := stripPoissonKernel_integrable hbelow habove
  have hconst := hk.const_mul (Real.log Real.pi)
  have hdifference := hconst.sub hgamma
  apply hdifference.congr
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0]
    with T hT
  have hidentity :
      lowerGammaBoundaryLog 1 1 T =
        Real.log Real.pi - lowerRiemannLog T 0 := by
    simpa using!
      (lowerGammaBoundaryLog_integer_scaled
        (k := 1) (by norm_num) (R := (1 : ℝ))
        (by norm_num) hT)
  change
    Real.log Real.pi * stripPoissonKernel σ T -
        stripPoissonKernel σ T * lowerGammaBoundaryLog 1 1 T =
      stripPoissonKernel σ T * lowerRiemannLog T 0
  rw [hidentity]
  ring
end CohnElkies
