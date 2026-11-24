-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.herm_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:46:40.313998+00:00
-- url     : https://prove2.me/submissions/e093791b-fa7d-443a-8b71-02c2068a02cd

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure

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
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (u v v' : ι → ℂ) : herm H u (v + v') = herm H u v + herm H u v' := by
  simp [herm]
end Formalism.FourierDecayAlt.P.B2x8
