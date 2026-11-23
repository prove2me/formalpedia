-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx3.semb_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:20.067096+00:00
-- url     : https://prove2.me/submissions/b63d98e3-88bf-4efd-8a9d-9b5f99d6002f

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx3
namespace Formalism.FourierDecayAlt.P.Jx3
theorem _root_.solution (E : Type) [Field E] [NumberField E] (c : ℝ) (t : E) : semb E c t = c • cemb E t := by
  simp [semb]
end Formalism.FourierDecayAlt.P.Jx3
