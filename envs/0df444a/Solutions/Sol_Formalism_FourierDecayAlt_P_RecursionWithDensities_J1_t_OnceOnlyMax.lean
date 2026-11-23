-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.J1.t_OnceOnlyMax
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:27.469801+00:00
-- url     : https://prove2.me/submissions/4bdf7545-773c-46f1-9a79-f1fed9f1d24f

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexOrder ComplexConjugate
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
theorem _root_.solution : OnceOnlyMax := by
  intro hO P _ B hpos hk hA
  have h := hO P B hpos hk hA
  have hA' := hA
  unfold S3.MassData.InTheoremA S3.MassData.Smod at hA'
  have hp := hpos.2
  have hvN : 0 < B.volN := by tauto
  have hvH : 0 < B.volH := by tauto
  have hvN' : 0 < B.volN' := by tauto
  have hvH' : 0 < B.volH' := by tauto
  have hd : 0 < B.dimπ := by tauto
  have hd' : 0 < B.dimπ' := by tauto
  have hn : 0 < B.n0c := by tauto
  have hδ : 0 ≤ B.δ := by tauto
  have c0 : 0 ≤ B.c0 * B.c0' := by unfold S3.MassData.c0 S3.MassData.c0'; positivity
  have h5 : 0 ≤ (1 + B.δ) * B.IntN := le_trans (mul_nonneg c0 hk.2) hA'
  refine h.trans ?_
  have h6 : (1 + B.δ) * B.supdens * (B.n0c * B.IntN) = B.supdens * (B.n0c * ((1 + B.δ) * B.IntN)) := by ring
  have h7 : (1 + B.δ) * max B.supdens 1 * (B.n0c * B.IntN) = max B.supdens 1 * (B.n0c * ((1 + B.δ) * B.IntN)) := by ring
  rw [h6, h7]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hn.le h5)
end Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
