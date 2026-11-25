-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.decay_minimum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:37:46.083849+00:00
-- url     : https://prove2.me/submissions/69bb4549-3419-47bb-8e77-dce5655c7c03

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetTopConvergence
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux7_decayMin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism.FourierDecayAlt.P.Ux7
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.U.DecayMin := by
  exact decayMin
end Formalism.FourierDecayAlt.P
