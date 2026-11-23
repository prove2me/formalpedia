-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiscFubiniVolume.hasDerivAt_g0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:54.510443+00:00
-- url     : https://prove2.me/submissions/2aad9ea2-2bcc-4d2a-bcc3-a995c880b191

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
theorem _root_.solution {t : ℝ} (ht : t ^ 2 < 1) : HasDerivAt g0 (g1 t) t := by
  have hp : 0 < 1 - t ^ 2 := by linarith
  have hs : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.2 hp
  have h2 := (hp1 t).sqrt hp.ne'
  have e : g1 t = -(2 * t) / (2 * Real.sqrt (1 - t ^ 2)) := by
    unfold g1; field_simp
  rw [e]; exact h2
end Formalism.FourierDecayAlt.P.DiscFubiniVolume
