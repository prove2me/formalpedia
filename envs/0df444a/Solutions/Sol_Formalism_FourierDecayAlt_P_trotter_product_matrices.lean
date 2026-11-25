-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.trotter_product_matrices
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:00:08.211903+00:00
-- url     : https://prove2.me/submissions/6867f311-2d32-4a5f-b54c-d39cf82e037b

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GroupGeneratedByExp
import Theorems.Thm_Formalism_FourierDecayAlt_P_GroupGeneratedByExp_trotterMx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Qr.TrotterMx := by
  intro N X Y
  exact GroupGeneratedByExp.trotterMx N X Y
end Formalism.FourierDecayAlt.P
