-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.planeWaveWord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:49:34.604645+00:00
-- url     : https://prove2.me/submissions/8cd7ae2d-0937-493a-a89e-133f1cf6e2e5

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_lift_reduction_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_liftMatrix_diagonal_eq_diagScalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_comm_insL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_cen_Um
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_cen_Uinv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_freeOf_transfer_word_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_RRw
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_Vw
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_Viw
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_insL_Um_Uinv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_insL_Uinv_Um
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_plus_TT
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_minus_TT
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_plus_RR
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_minus_RR
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_Vw_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_Viw_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution (QQ : K → M2 A) (f fi : A) (s : K) (w : List (Letter K S))
    (hW : IsWave f fi) (hQ : WaveQQ QQ f fi s) (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) :
    Vw f s w * Viw fi s w = 1 ∧ Viw fi s w * Vw f s w = 1 ∧
    star (Vw f s w) * RRw QQ w * Vw f s w = RRw QQ w ∧
    ∀ Y, d0 (Viw fi s w) * TTw QQ w Y * d0 (Vw f s w) =
      lift0 (Um (A := A) s)ᴴ * TTw QQ w Y * lift0 (Um (A := A) s) := by
  induction w with
  | nil =>
    obtain ⟨h1, h2, h3⟩ := hW
    have eV : (Vw f s ([] : List (Letter K S)) : SlopeTestRemainingChoices S A) = io f := mul_one _
    have eVi : (Viw fi s ([] : List (Letter K S)) : SlopeTestRemainingChoices S A) = io fi := one_mul _
    rw [eV, eVi]
    refine ⟨by rw [← io_mul, h1, io_one], by rw [← io_mul, h2, io_one], ?_, ?_⟩
    · show star (io f) * 1 * io f = 1
      rw [io_star, h3, mul_one, ← io_mul, h2, io_one]
    · intro Y
      show d0 (io fi) * lift0 (QQ Y) * d0 (io f) = _ * lift0 (QQ Y) * _
      rw [← liftMatrix_diagonal_eq_diagScalar, ← liftMatrix_diagonal_eq_diagScalar, ← lift_reduction_mul, ← lift_reduction_mul, hQ Y, lift_reduction_mul, lift_reduction_mul]
  | cons l w ih =>
    rw [List.map_cons, List.nodup_cons] at hw
    obtain ⟨h1, h2, h3, h4⟩ := ih hw.2
    have hV := free_Vw f s w l.intersection_update_fsHerm_neg_one hw.1
    have hVi := free_Viw fi s w l.intersection_update_fsHerm_neg_one hw.1
    have hRR := free_RRw QQ w l.intersection_update_fsHerm_neg_one hw.1
    have hT := freeOf_transfer_word_matrix QQ w l.intersection_update_fsHerm_neg_one hw.1
    rw [Vw_cons, Viw_cons]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mul_assoc, (comm_insL (cen_Um _) hV).left_comm, h1, mul_one, insL_Uinv_Um]
    · rw [mul_assoc, (comm_insL (cen_Uinv _) hVi).left_comm, h2, mul_one, insL_Um_Uinv]
    · unfold RRw
      by_cases hl : l.plus
      · simp only [hl, if_true]
        exact plus_RR l.intersection_update_fsHerm_neg_one s hV hVi hRR (hT _) h1 h3 (h4 _)
      · simp only [hl, Bool.false_eq_true, if_false]
        exact minus_RR l.intersection_update_fsHerm_neg_one s hV hVi hRR (hT _) h1 h3 (h4 _)
    · intro Y
      unfold TTw
      by_cases hl : l.plus
      · simp only [hl, if_true]
        exact plus_TT l.intersection_update_fsHerm_neg_one s _ hV (hT _) (h4 _)
      · simp only [hl, Bool.false_eq_true, if_false]
        exact minus_TT l.intersection_update_fsHerm_neg_one s _ hV hVi (hT _) (h4 _)
end Formalism.FourierDecayAlt.P.Wd11
