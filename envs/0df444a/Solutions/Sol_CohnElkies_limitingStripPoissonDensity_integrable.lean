-- Prove2me | solution 1 for CohnElkies.limitingStripPoissonDensity_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/eb1296d1-9f46-46f5-81af-f3a7ec90a870

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripNormalizedPoissonExtension_one
import Theorems.Thm_CohnElkies_stripNormalizedPoissonExtension_le_majorant
import Theorems.Thm_CohnElkies_stripPoissonExponentialMajorant_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution :
    Integrable limitingStripPoissonDensity := by
  have hcontinuous : Continuous limitingStripPoissonDensity := by
    unfold limitingStripPoissonDensity
    apply Continuous.div continuous_const
    · fun_prop
    · intro T
      have hcosh := Real.one_le_cosh (Real.pi * T / 2)
      positivity
  apply stripPoissonExponentialMajorant_integrable.mono'
    hcontinuous.aestronglyMeasurable
  filter_upwards [] with T
  have h := stripNormalizedPoissonExtension_le_majorant
    (σ := (1 : ℝ)) (by norm_num) (by norm_num) T
  rw [stripNormalizedPoissonExtension_one] at h
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2
end CohnElkies
