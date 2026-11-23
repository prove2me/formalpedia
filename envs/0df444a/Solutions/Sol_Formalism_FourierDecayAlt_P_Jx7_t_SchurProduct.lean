-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.t_SchurProduct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:55.648517+00:00
-- url     : https://prove2.me/submissions/0b71ae09-1ee6-42f3-939a-2ee019344713

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_prod

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
open scoped ComplexOrder ComplexConjugate Matrix
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution : SchurProduct := by
  intro α P _ F k hk
  exact psd_prod univ k (fun p _ => hk p)
end Formalism.FourierDecayAlt.P.Jx7
