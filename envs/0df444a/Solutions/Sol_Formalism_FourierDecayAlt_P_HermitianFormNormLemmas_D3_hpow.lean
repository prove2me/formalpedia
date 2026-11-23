-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3.hpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:52:59.8658+00:00
-- url     : https://prove2.me/submissions/1585bcdc-bf8e-4a9c-8eb4-c52e2cd4ed46

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3
theorem _root_.solution {b x c : ℝ} (hb : 1 < b) (hx0 : 0 ≤ x) (hx : x ≤ b ^ c) (n : ℕ) {K M : ℝ}
    (h : c * n ≤ K * M) : x ^ n ≤ Real.exp (K * M * Real.log b) := by
  have hb0 : 0 < b := by linarith
  have hlog : 0 < Real.log b := Real.log_pos hb
  calc x ^ n ≤ (b ^ c) ^ n := by gcongr
    _ = b ^ (c * (n : ℝ)) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
    _ = Real.exp (Real.log b * (c * (n : ℝ))) := Real.rpow_def_of_pos hb0 _
    _ ≤ Real.exp (K * M * Real.log b) := by
      apply Real.exp_le_exp.mpr
      nlinarith
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3
