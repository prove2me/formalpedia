-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.a2one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:57:55.759633+00:00
-- url     : https://prove2.me/submissions/821507ad-b35b-4450-95a9-f32b865c68e4

import Definitions.Def_Formalism_HermitianCurvature_StatementA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondKernelPropertyKernel
import Theorems.Thm_Formalism_FourierDecayAlt_P_LastBlockReversalIndices_a2one_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_ReversedIndexLastBlock_pt_inv_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ReversedIndexLastBlock
open Formalism.DoubleCosetMeasures
namespace Formalism.FourierDecayAlt.P.ReversedIndexLastBlock
theorem _root_.solution : Formalism.FourierDecayAlt.A.LevelOneKernelPoint :=
  Formalism.FourierDecayAlt.P.LastBlockReversalIndices.a2one_of (fun _ _ l t N hN => pt_inv_last l t N hN)
end Formalism.FourierDecayAlt.P.ReversedIndexLastBlock
