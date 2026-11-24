-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.Em_mul_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:47:33.872469+00:00
-- url     : https://prove2.me/submissions/55cedaea-d034-4306-8226-92646d6b8881

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
theorem _root_.solution {X : Type*} (A : Matrix (Fin (k + 1)) X ℂ) (i : Fin (2 * r + k + 1)) (x : X) (hi : ¬ mid k r i) :
    (Em k r * A) i x = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Em, if_neg, zero_mul]
  intro h
  exact hi (h ▸ mid_wI b)
end Formalism.FourierDecayAlt.P.B2x3
