-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_twistMat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:48.328318+00:00
-- url     : https://prove2.me/submissions/32bbd986-a575-439f-9df5-c560ee973fc2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_gL_mul_gLinv
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_gLinv_mul_gL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (j : Fin n) (k : ℤ) :
    twistMat R n j k * twistMat R n j (-k) = 1 := by
  have hd : Matrix.diagonal (fun a => if a = j then (LaurentPolynomial.T k : GLLaurent R n) else 1) *
      Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T (-k) else 1) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs
    · rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
    · rw [one_mul]
  unfold twistMat
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (gLinv R n) (gL R n), flt_gLinv_mul_gL, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _), hd, Matrix.one_mul, flt_gL_mul_gLinv]
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
