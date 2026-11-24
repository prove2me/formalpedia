-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.hb_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:47:27.82691+00:00
-- url     : https://prove2.me/submissions/e796184f-68db-45a9-ba44-216d553055ef

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
theorem _root_.solution (v w : Fin (k + 1) → ℂ) :
    star w ⬝ᵥ (Hb k *ᵥ v) =
      (∑ i : Fin k, star (w i.castSucc) * v i.castSucc) - star (w (Fin.last k)) * v (Fin.last k) := by
  unfold Hb
  simp only [dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_castSucc, Pi.star_apply, if_true]
  have h : ∀ i : Fin k, (if i.castSucc = Fin.last k then (-1 : ℂ) else 1) = 1 := fun i =>
    if_neg (Fin.castSucc_lt_last i).ne
  simp only [h, one_mul]
  ring
end Formalism.FourierDecayAlt.P.B2x3
