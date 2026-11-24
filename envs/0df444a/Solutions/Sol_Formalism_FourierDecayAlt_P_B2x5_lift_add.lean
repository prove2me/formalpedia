-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.lift_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:05:59.803007+00:00
-- url     : https://prove2.me/submissions/70f69331-d611-44b2-94f1-4ea0dfd5b6aa

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (k r' : ℕ) (y y' : Fin (2 * r' + k + 1) → ℂ) :
    liftVec k 1 r' (y + y') = liftVec k 1 r' y + liftVec k 1 r' y' := by
  funext p
  simp only [liftVec, Pi.add_apply]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.B2x5
