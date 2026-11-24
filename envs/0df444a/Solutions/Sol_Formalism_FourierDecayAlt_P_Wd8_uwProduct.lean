-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.uwProduct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:07.512523+00:00
-- url     : https://prove2.me/submissions/6b6362e8-1d41-4fe3-bc2a-f19ec56bf1b4

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_word_product_formula_general

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd8
theorem _root_.solution : UwProduct := by
  intro K A S _ _ _ _ _ _ _ _ QQ sites w hOK hw z
  rw [word_product_formula_general sites w hOK.2 hw.1 z]
  by_cases hc : ∀ c, c ∉ w.map Letter.intersection_update_fsHerm_neg_one → z c = 0
  · rw [if_pos hc, if_pos hc]
    congr 1
    refine List.map_congr_left fun l _ => ?_
    by_cases h : l.plus = true
    · have e : lm l = fun σ : Site A => Ts σ l.pt := funext fun σ => if_pos h
      rw [e, if_pos h]
      rfl
    · have e : lm l = fun σ : Site A => (Ts σ l.pt).map star := funext fun σ => if_neg h
      rw [e, if_neg h]
  · rw [if_neg hc, if_neg hc]
end Formalism.FourierDecayAlt.P.Wd8
