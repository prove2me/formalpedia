-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.A3.ds_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:47:21.30946+00:00
-- url     : https://prove2.me/submissions/09658069-6151-4a9e-a527-32bb7a50955f

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_A3_dS_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2 Formalism.FourierDecayAlt.P.LEx2.A3
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx2.A3
theorem _root_.solution {B : Base} (S : Step B) (Y : ℝ) : S.ds Y 0 = S.gX Y := dS_zero B _ _
end Formalism.FourierDecayAlt.P.LEx2.A3
