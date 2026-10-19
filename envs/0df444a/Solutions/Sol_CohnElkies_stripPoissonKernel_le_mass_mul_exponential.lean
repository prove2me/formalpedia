-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_le_mass_mul_exponential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/61c438ac-647f-4373-b7d3-83e0adf4db47

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripBottomMass_pos
import Theorems.Thm_CohnElkies_stripNormalizedPoissonKernel_eq_extension
import Theorems.Thm_CohnElkies_stripNormalizedPoissonExtension_le_majorant

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
    {σ : ℝ} (hzero : 0 ≤ σ) (habove : σ < 1)
    (T : ℝ) :
    stripPoissonKernel σ T ≤
      stripBottomMass σ * stripPoissonExponentialMajorant T := by
  have hbelow : -1 < σ := by linarith
  have hmass := stripBottomMass_pos habove
  have hnormalize := stripNormalizedPoissonKernel_eq_extension
    hbelow habove T
  have hbound := stripNormalizedPoissonExtension_le_majorant
    hzero habove.le T
  have hquotient :
      stripPoissonKernel σ T / stripBottomMass σ ≤
        stripPoissonExponentialMajorant T := by
    change stripNormalizedPoissonKernel σ T ≤
      stripPoissonExponentialMajorant T
    rw [hnormalize]
    exact hbound.2
  have h := (div_le_iff₀ hmass).mp hquotient
  nlinarith
end CohnElkies
