-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx2.t_MajIsProf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:41.446264+00:00
-- url     : https://prove2.me/submissions/78a69345-78a8-44f4-8c1e-34ae812b764e

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx2
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped nonZeroDivisors ComplexConjugate
namespace Formalism.FourierDecayAlt.P.Jx2
theorem _root_.solution : MajIsProf := by
  intro E W _ _ D e hP ρ l
  simp only [TB.Data.maj, prof]
  refine Fintype.prod_equiv e _ _ (fun v => ?_)
  simp only [hP v l, Equiv.symm_apply_apply]
end Formalism.FourierDecayAlt.P.Jx2
