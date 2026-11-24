-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.factorialCancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:41.72542+00:00
-- url     : https://prove2.me/submissions/1780294c-5af9-45e7-a436-4ac37a4adf57

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Sz.FactorialCancel := by
  intro k n hkn
  unfold sfac
  rw [mul_comm]
  exact Finset.prod_range_mul_prod_Ico _ hkn
end Formalism.FourierDecayAlt.P
