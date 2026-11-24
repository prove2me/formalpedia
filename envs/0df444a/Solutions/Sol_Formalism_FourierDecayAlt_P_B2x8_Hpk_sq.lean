-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.Hpk_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:47:18.253504+00:00
-- url     : https://prove2.me/submissions/23c63799-fe41-4ca9-94f7-6b8b11e779ad

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (k r : ℕ) : Hpk k r * Hpk k r = 1 := (Formalism.QuantumDeterminants.hpkFacts k r).2.1
end Formalism.FourierDecayAlt.P.B2x8
