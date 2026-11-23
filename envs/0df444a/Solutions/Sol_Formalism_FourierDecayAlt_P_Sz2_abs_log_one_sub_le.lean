-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz2.abs_log_one_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:28.94235+00:00
-- url     : https://prove2.me/submissions/a9d7d21f-2950-46c6-97ca-0d51fe3c806c

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz2
theorem _root_.solution {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    |Real.log (1 - x)| ≤ 2 * x := by
  have hpos : 0 < 1 - x := by linarith
  have hle : Real.log (1 - x) ≤ 0 := Real.log_nonpos hpos.le (by linarith)
  rw [abs_of_nonpos hle]
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h2
  have h3 : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith
  linarith
end Formalism.FourierDecayAlt.P.Sz2
