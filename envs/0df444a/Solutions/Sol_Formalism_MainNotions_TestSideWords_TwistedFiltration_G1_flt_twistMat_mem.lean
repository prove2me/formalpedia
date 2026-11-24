-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_twistMat_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:27:22.555091+00:00
-- url     : https://prove2.me/submissions/f26c44b0-f7b2-49bf-abf0-8f4bbed6a60f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_T_mem_laurentFiltration
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_L_C


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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (j : Fin n) (k e t : ℤ) (h0 : t ≤ 0) (hk : t ≤ e * k)
    (b c : Fin n) : twistMat R n j k b c ∈ (flt_L (GLCoord R n) e).F t := by
  unfold twistMat
  rw [Matrix.mul_apply]
  refine sum_mem fun a _ => ?_
  rw [Matrix.mul_diagonal]
  have hg : gL R n b a ∈ (flt_L (GLCoord R n) e).F 0 := by
    simp only [gL, Matrix.map_apply]
    exact flt_L_C e _
  have hgi : gLinv R n a c ∈ (flt_L (GLCoord R n) e).F 0 := by
    simp only [gLinv, Matrix.map_apply]
    exact flt_L_C e _
  have hd : (if a = j then LaurentPolynomial.T k else 1) ∈ (flt_L (GLCoord R n) e).F t := by
    split_ifs
    · exact (flt_L (GLCoord R n) e).anti hk (T_mem_laurentFiltration e k)
    · exact (flt_L (GLCoord R n) e).anti h0 (flt_L (GLCoord R n) e).one_mem
  have hm := (flt_L (GLCoord R n) e).mul_mem ((flt_L (GLCoord R n) e).mul_mem hg hd) hgi
  rwa [zero_add, add_zero] at hm
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
