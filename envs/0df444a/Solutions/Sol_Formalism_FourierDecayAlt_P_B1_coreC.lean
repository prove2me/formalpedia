-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B1.coreC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:58:57.176469+00:00
-- url     : https://prove2.me/submissions/92a43a45-11f6-4a4e-9de9-045570e764e1

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_semi
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_polar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B1
theorem _root_.solution : FormCoreC := core semi polar
end Formalism.FourierDecayAlt.P.B1
