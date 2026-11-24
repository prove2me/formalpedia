-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.pj_dens_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:41:37.068146+00:00
-- url     : https://prove2.me/submissions/94d0216a-f6e0-4c34-9333-8a04502dd17c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_PjDensUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (t p q r : ℝ) (ht : 0 < t) :
    (p + q + r) ^ 2 ≤ (1 + t) * p ^ 2 + (1 + 1 / t) * (2 * q ^ 2 + 2 * r ^ 2) := by
  have h1 : 2 * p * (q + r) ≤ t * p ^ 2 + (q + r) ^ 2 / t := by
    rw [← sub_nonneg]
    have : t * p ^ 2 + (q + r) ^ 2 / t - 2 * p * (q + r) = (t * p - (q + r)) ^ 2 / t := by
      field_simp
      ring
    rw [this]
    positivity
  have h2 : (q + r) ^ 2 ≤ 2 * q ^ 2 + 2 * r ^ 2 := by nlinarith [sq_nonneg (q - r)]
  have h3 : (1 + 1 / t) * (q + r) ^ 2 ≤ (1 + 1 / t) * (2 * q ^ 2 + 2 * r ^ 2) := by
    have : 0 ≤ 1 + 1 / t := by positivity
    exact mul_le_mul_of_nonneg_left h2 this
  calc (p + q + r) ^ 2 = p ^ 2 + 2 * p * (q + r) + (q + r) ^ 2 := by ring
    _ ≤ p ^ 2 + (t * p ^ 2 + (q + r) ^ 2 / t) + (q + r) ^ 2 := by linarith
    _ = (1 + t) * p ^ 2 + (1 + 1 / t) * (q + r) ^ 2 := by ring
    _ ≤ _ := by linarith
end Formalism.MainNotions.LeviCoordinates
