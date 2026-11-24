-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:55:03.929995+00:00
-- url     : https://prove2.me/submissions/78f9f644-8ac4-4e88-bf41-ac13aa8630f6

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellHermitian_bigCell_mulVec_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_jV_wbPart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BigCellHermitian
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.TwoByOneBlock
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.BigCellHermitian
theorem _root_.solution (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z z' : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (hz' : inWb k r z') :
    herm (Hpk k r) (bigCell k r c μ *ᵥ z') z = herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z) := by
  conv_lhs => rw [← jV_wbPart hz', ← jV_wbPart hz]
  rw [bigCell_mulVec_jV, herm_jV]
end Formalism.FourierDecayAlt.P.BigCellHermitian
