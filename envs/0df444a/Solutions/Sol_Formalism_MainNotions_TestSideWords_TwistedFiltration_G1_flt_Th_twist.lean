-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_Th_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:06.761265+00:00
-- url     : https://prove2.me/submissions/4c2ddb29-a6f5-4da0-ac88-cedd779ece0b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_sum_C_C_mul_sum_of_mul_eq_one
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_twistMat_mul


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
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n) :
    (MvPolynomial.map (twistSub (R := R) LL S j)).comp (flt_tay R (ι × Fin n)) =
      (flt_Th LL S j).comp (twistSub (R := R) LL S j) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [flt_tay, flt_Th, twistSub]
  · intro v
    have hY1 := sum_C_C_mul_sum_of_mul_eq_one (σ' := ι × Fin n) (σ'' := ι × Fin n) (twistMat R n j 1) (twistMat R n j (-1))
      (by simpa using flt_twistMat_mul R n j (-1)) (fun c => X (v.1, c)) v.2
    have hM : twistMat R n j (-1) * twistMat R n j 1 = 1 := by simpa using flt_twistMat_mul R n j (-1)
    have hY2 := sum_C_C_mul_sum_of_mul_eq_one (σ' := ι × Fin n) (σ'' := ι × Fin n) (Matrix.transpose (twistMat R n j (-1)))
      (Matrix.transpose (twistMat R n j 1))
      (by rw [← Matrix.transpose_mul, hM, Matrix.transpose_one]) (fun c => X (v.1, c)) v.2
    simp only [Matrix.transpose_apply] at hY2
    by_cases hS : v.1 ∈ S
    · by_cases hv : LL.vec v.1 = true
      · simp [flt_tay, flt_Th, twistSub, hS, hv, mul_add, Finset.sum_add_distrib, hY1]
      · simp [flt_tay, flt_Th, twistSub, hS, hv, mul_add, Finset.sum_add_distrib, hY2]
    · simp [flt_tay, flt_Th, twistSub, hS]
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
