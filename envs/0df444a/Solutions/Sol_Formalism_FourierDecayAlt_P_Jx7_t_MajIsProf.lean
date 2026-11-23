-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.t_MajIsProf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:21.584079+00:00
-- url     : https://prove2.me/submissions/a827c52a-091b-484e-b013-1cb58444e6a3

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution : MajIsProf := by
  intro E W _ _ D e hP ρ l
  unfold TB.Data.maj prof
  rw [← Equiv.prod_comp e]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [Equiv.symm_apply_apply]
  rw [hP v l]
end Formalism.FourierDecayAlt.P.Jx7
