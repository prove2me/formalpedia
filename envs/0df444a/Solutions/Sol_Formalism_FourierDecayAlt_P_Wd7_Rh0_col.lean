-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.Rh0_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:54:10.9598+00:00
-- url     : https://prove2.me/submissions/46272d04-ff76-40cc-84e5-223c9e5ca75c

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Wd7_eU_apply__f51f2867f050
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_smul_cancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (a : S) (D : K) (hD : D ≠ 1) (m : Fin 2) (z : Ix S) :
    (Rh0 a D m 0 : SlopeTestRemainingChoices S A) z e1 = if m = 0 ∧ z = e1 then 1 else 0 := by
  have h : (Rh0 a D m 0 : SlopeTestRemainingChoices S A) z e1 =
      (D - 1)⁻¹ • (D • ((1 : M2 (SlopeTestRemainingChoices S A)) m 0) z e1 - (eU a 0 m : SlopeTestRemainingChoices S A) z e1) := rfl
  have hu : Function.update (e1 : Ix S) a 0 = e1 := Function.update_eq_self a e1
  have he : (e1 : Ix S) a = 0 := rfl
  rw [h, eU_apply', Matrix.one_apply, he, hu]
  by_cases hm : m = 0
  · subst hm
    by_cases hz : z = e1
    · subst hz
      simp only [if_true, and_self, Matrix.one_apply_eq]
      exact smul_cancel D hD 1
    · simp [hz]
  · have hm' : ¬ (0 = m) := fun h => hm h.symm
    simp [hm, hm']
end Formalism.FourierDecayAlt.P.Wd7
