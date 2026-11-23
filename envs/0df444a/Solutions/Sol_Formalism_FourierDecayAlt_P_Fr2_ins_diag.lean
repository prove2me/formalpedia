-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.ins_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:42.586593+00:00
-- url     : https://prove2.me/submissions/bf8c5cbe-a580-4a87-a1d3-3fe45cd15c00

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_eU_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Finset Formalism.FourierDecayAlt.I Formalism.FourierDecayAlt.P.Interlace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr2
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr2
theorem _root_.solution (a : S) (X Y : Ix S → A) :
    ins a !![Matrix.diagonal X, 0; 0, Matrix.diagonal Y] =
      Matrix.diagonal (fun e => if e a = 0 then X e else Y e) := by
  simp only [ins, Fin.sum_univ_two, eU_diag]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one,
    mul_zero, add_zero, zero_add, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]
  congr 1; funext e
  by_cases h : e a = 0
  · simp [h]
  · have h1 : e a = 1 := Fin.eq_one_of_ne_zero _ h
    simp [h1]
end Formalism.FourierDecayAlt.P.Fr2
