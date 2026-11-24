-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.Em_mul_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:13:43.203387+00:00
-- url     : https://prove2.me/submissions/13f61568-cdd3-4c09-bf14-0dbdc4586596

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_wI_midx
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_wI_inj

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
theorem _root_.solution {X : Type*} (A : Matrix (Fin (k + 1)) X ℂ) (i : Fin (2 * r + k + 1)) (x : X) (hi : mid k r i) :
    (Em k r * A) i x = A (midx hi) x := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (midx hi)]
  · rw [Em, if_pos (wI_midx hi).symm, one_mul]
  · intro b _ hb
    rw [Em, if_neg, zero_mul]
    intro h
    apply hb
    apply wI_inj (r := r)
    rw [wI_midx hi, h]
  · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.B2x3
