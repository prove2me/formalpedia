-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.thetaMono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:42:12.202813+00:00
-- url     : https://prove2.me/submissions/a3bafd34-0ed5-434f-832c-c70c114e907f

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution : ThetaMono := by
  intro σ ε ε' x hσ hε hεε hx
  unfold th
  have h1 : 0 < x + ε := by linarith
  have h2 : 0 < x + ε' := by linarith
  refine Real.rpow_le_rpow (div_nonneg hx.le h2.le) ?_ hσ
  exact div_le_div_of_nonneg_left hx.le h1 (by linarith)
end Formalism.FourierDecayAlt.P.LEx1
