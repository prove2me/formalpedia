-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.uwb_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:15:41.469008+00:00
-- url     : https://prove2.me/submissions/75c984ae-43a4-46d2-b1bb-9163d23a9556

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_mulVec_bvec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_bvec_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_hpk_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_hpk_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_not_mid_cases
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_fix_dual

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
theorem _root_.solution {g : Mat k r} (hg : g ∈ UWb k r) (i l : Fin (2 * r + k + 1)) (hi : ¬ mid k r i) :
    g i l = if i = l then 1 else 0 := by
  have key : ∀ j : Fin (2 * r + k + 1), gᴴ *ᵥ bvec j = bvec j → g j l = if j = l then 1 else 0 := by
    intro j hj
    have h := congrFun hj l
    rw [mulVec_bvec, bvec_apply, Matrix.conjTranspose_apply] at h
    have h2 := congrArg star h
    rw [star_star] at h2
    rw [h2]
    by_cases e : l = j
    · rw [if_pos e, if_pos e.symm, star_one]
    · rw [if_neg e, if_neg (fun e' => e e'.symm), star_zero]
  obtain ⟨a, rfl | rfl⟩ := not_mid_cases i hi
  · apply key
    have := fix_dual hg.1 (hg.2 a).2
    rwa [hpk_es] at this
  · apply key
    have := fix_dual hg.1 (hg.2 a).1
    rwa [hpk_e] at this
end Formalism.FourierDecayAlt.P.B2x3
