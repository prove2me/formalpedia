-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.minors_first_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:21:28.07568+00:00
-- url     : https://prove2.me/submissions/7c3e4e8a-3e35-4770-8c38-f95faea78413

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SignPermutationIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPolynomialExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_succAbove_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_zb_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution : MinorsFirstCase := by
  intro i0 s' h t c
  by_cases hc : c.val = i0
  · rw [if_pos hc, ← zb_det i0 s' h t]
    congr 1
    ext a l
    simp only [Matrix.of_apply, succAbove_val, hc]
    have hl := l.isLt
    by_cases hl0 : (l : ℕ) < i0
    · simp only [hl0, if_true]
      unfold Zb
      split_ifs <;> first | rfl | omega
    · simp only [hl0, if_false]
      unfold Zb
      split_ifs <;> first | rfl | omega
  · rw [if_neg hc]
    have hne : (⟨i0, by omega⟩ : Fin (i0 + s' + 1)) ≠ c := fun e => hc (by rw [← e])
    obtain ⟨l0, hl0⟩ := Fin.exists_succAbove_eq hne
    apply Matrix.det_eq_zero_of_column_eq_zero l0
    intro a
    simp only [Matrix.of_apply, hl0]
    have ha := a.isLt
    unfold Zb
    split_ifs <;> first | rfl | omega
end Formalism.FourierDecayAlt.P.SignAntidiagonal
