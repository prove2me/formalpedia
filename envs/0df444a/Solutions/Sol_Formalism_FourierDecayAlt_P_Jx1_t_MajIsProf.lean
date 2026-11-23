-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx1.t_MajIsProf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:22.517772+00:00
-- url     : https://prove2.me/submissions/7940025c-91ef-4478-9228-8f6d7b92c130

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx1
namespace Formalism.FourierDecayAlt.P.Jx1
theorem _root_.solution : MajIsProf := by
  unfold MajIsProf
  intro E W _ _ D e hP ρ l
  unfold TB.Data.maj prof
  refine Fintype.prod_equiv e _ _ (fun v => ?_)
  simp only [hP v l, Equiv.symm_apply_apply]
end Formalism.FourierDecayAlt.P.Jx1
