-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.herm_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:47:24.712853+00:00
-- url     : https://prove2.me/submissions/65c8ee73-635a-4728-b352-bbbae212a16e

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
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (u v v' : ι → ℂ) : herm H u (v + v') = herm H u v + herm H u v' := by
  simp only [herm, star_add, add_dotProduct]
end Formalism.FourierDecayAlt.P.B2x5
