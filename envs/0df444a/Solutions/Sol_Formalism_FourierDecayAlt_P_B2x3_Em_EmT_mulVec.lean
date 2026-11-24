-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.Em_EmT_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:23:16.485817+00:00
-- url     : https://prove2.me/submissions/7faf0d3e-e708-493c-815c-c207926a38f0

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_wI_midx
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_wI_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_EmT_mulVec

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
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) : Em k r *ᵥ ((Em k r)ᵀ *ᵥ z) = z := by
  ext i
  by_cases hi : mid k r i
  · rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (midx hi)]
    · rw [Em, if_pos (wI_midx hi).symm, one_mul, EmT_mulVec, wI_midx]
    · intro b _ hb
      rw [Em, if_neg, zero_mul]
      intro h
      apply hb
      apply wI_inj (r := r)
      rw [wI_midx hi, h]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [hz i (by omega)]
    rw [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro b _
    rw [Em, if_neg, zero_mul]
    intro h
    exact hi (h ▸ mid_wI b)
end Formalism.FourierDecayAlt.P.B2x3
