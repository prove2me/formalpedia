-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.midx_wI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:31:23.213835+00:00
-- url     : https://prove2.me/submissions/5676468f-91b1-4e7a-a5ee-17216bda6bf5

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution (m : Fin (k + 1)) : midx (mid_wI (r := r) m) = m := by
  apply Fin.ext
  simp only [wI, midx]
  omega
end Formalism.FourierDecayAlt.P.B2x3
