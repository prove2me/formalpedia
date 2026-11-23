-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.A.ds_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:03.033785+00:00
-- url     : https://prove2.me/submissions/eb62c124-47e1-4813-ae8e-89369263b059

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_A_dS_zero__83ca01

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2 Formalism.FourierDecayAlt.P.LEx2.A
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx2.A
theorem _root_.solution {B : Base} (S : Step B) (Y : ℝ) : S.ds Y 0 = S.gX Y := dS_zero B _ _
end Formalism.FourierDecayAlt.P.LEx2.A
