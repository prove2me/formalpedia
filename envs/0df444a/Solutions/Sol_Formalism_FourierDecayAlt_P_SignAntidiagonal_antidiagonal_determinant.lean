-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.antidiagonal_determinant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:49:38.075865+00:00
-- url     : https://prove2.me/submissions/ac8861e3-4017-4fd2-a51b-39acbe9d943f

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SignPermutationIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_sgnW_succ

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
theorem _root_.solution : AntiDiagDet := by
  intro m
  induction m with
  | zero => simp [sgnW]
  | succ m ih =>
    rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last m)]
    · have hsub : ((Matrix.of fun a b : Fin (m + 1) => if a.val + b.val + 1 = m + 1 then (1 : ℂ) else 0).submatrix
          Fin.succ (Fin.last m).succAbove) =
          Matrix.of fun a b : Fin m => if a.val + b.val + 1 = m then (1 : ℂ) else 0 := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last, Fin.val_succ, Fin.val_castSucc]
        congr 1
        apply propext; omega
      rw [hsub, ih, sgnW_succ]
      simp
    · intro j _ hj
      have hne : (j : ℕ) ≠ m := by intro h; apply hj; ext; simp [h]
      simp [hne]
    · simp
end Formalism.FourierDecayAlt.P.SignAntidiagonal
