-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr4.plus_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:39.385696+00:00
-- url     : https://prove2.me/submissions/65e5e097-0644-443e-8769-57c5fd0ab8ba

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2RmatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_freeOf2_matrix_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_freeOf2_rmatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_l
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_DD
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_tz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_free


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr4
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr4
theorem _root_.solution (L : LevelData A r) {f : FrameData S A} {a c : S} (hc : c ≠ a) (h : f.Free c) (Ya : ℂ) :
    (f.plus L a Ya).Free c := by
  obtain ⟨hRR, hTT, hF, hFi, hx, hxi, hcc, hci, hee⟩ := id h
  have z := free_zero (A := A) c
  have o := free_one (A := A) c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact free_mul hRR (Wd1.ins_free hc _ (hTT Ya))
  · exact fun Y => freeOf2_mul (hTT Y) (freeOf2_rmatrix hc _)
  · exact free_mul (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries (free_io c _) z z (free_io c _))
      (freeOf2_matrix_entries o z (free_mul (free_io c _) (free_l L h Ya)) (free_io c _)))) hF
  · exact free_mul hFi (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries o z (free_neg (free_l L h Ya)) (free_io c _))
      (freeOf2_matrix_entries (free_io c _) z z (free_io c _))))
  · exact fun Y => free_mul (hx Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))
  · exact fun Y => free_mul (hxi Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))
  · exact free_mul hcc (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hxi _)) z z (hx _)))
  · exact free_mul hci (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hx _)) z z (hxi _)))
  · exact fun Y => Wd1.ins_free hc _ (freeOf2_matrix_entries (free_add (free_sub (hee Y) (free_DD h Y Ya)) (free_tz L c))
      (free_neg (free_smul _ o)) z (free_mul (free_mul (hxi _) (hee Y)) (hx _)))
end Formalism.FourierDecayAlt.P.Fr4
