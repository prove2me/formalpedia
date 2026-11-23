-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.continuous_powMulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:13.608125+00:00
-- url     : https://prove2.me/submissions/f62b56a7-f9a1-4695-98fb-b25d61aaa25c

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_strictUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution (m j : ℕ) : Continuous
    (fun z : (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) => (-(strictUpper z.1)) ^ j *ᵥ z.2) :=
  Continuous.matrix_mulVec ((((continuous_strictUpper _).comp continuous_fst).neg).pow j) continuous_snd
end Formalism.FourierDecayAlt.P.G7
