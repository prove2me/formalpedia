-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiscFubiniVolume.hasDerivAt_g1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:54.513724+00:00
-- url     : https://prove2.me/submissions/c0e11e26-ef66-4ca0-ab70-7219380940d5

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_hp1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory intervalIntegral Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiscFubiniVolume
namespace Formalism.FourierDecayAlt.P.DiscFubiniVolume
theorem _root_.solution {t : ℝ} (ht : t ^ 2 < 1) : HasDerivAt g1 (g2 t) t := by
  have hp : 0 < 1 - t ^ 2 := by linarith
  have hs : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.2 hp
  have hsq : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hp.le
  have h2 := (hasDerivAt_neg t).div ((hp1 t).sqrt hp.ne') hs.ne'
  have e : g2 t = (-1 * Real.sqrt (1 - t ^ 2) - -t * (-(2 * t) / (2 * Real.sqrt (1 - t ^ 2)))) /
      Real.sqrt (1 - t ^ 2) ^ 2 := by
    unfold g2
    set s := Real.sqrt (1 - t ^ 2)
    rw [hsq]
    field_simp
    nlinarith [hsq]
  rw [e]; exact h2
end Formalism.FourierDecayAlt.P.DiscFubiniVolume
