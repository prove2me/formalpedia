-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G8.psi_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:38.080208+00:00
-- url     : https://prove2.me/submissions/57234bf0-08a5-46fe-8e7a-e156300feb78

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G8
namespace Formalism.FourierDecayAlt.P.G8
theorem _root_.solution (β x y : ℂ) : psi β (x + y) = psi β x * psi β y := by
  simp only [psi, mul_add, Complex.add_re, Complex.ofReal_add, Complex.exp_add]
end Formalism.FourierDecayAlt.P.G8
