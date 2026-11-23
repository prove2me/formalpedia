-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.t_ProductDomination
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:57:49.224747+00:00
-- url     : https://prove2.me/submissions/551a1f4c-50b9-4508-879f-5138f56a12d2

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_prod_dom

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
theorem _root_.solution : ProductDomination := by
  intro α P _ F k K hk hd
  exact psd_prod_dom univ k K (fun p _ => hk p) (fun p _ => hd p)
end Formalism.FourierDecayAlt.P.Jx7
