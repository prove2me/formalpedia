-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.matrixSubst_transvection_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:00:04.411362+00:00
-- url     : https://prove2.me/submissions/22a8f375-4bcb-4fd1-b32e-9bc9c25e80c8

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_TwistSubEqMatrixSubst
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionX
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sum_C_one_col
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sum_C_one_row
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sum_C_single_col
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sum_C_single_row
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_X


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
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.G
variable {R B : Type*} [CommRing R] [CommRing B] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
  (φ : R →+* B) (a b : Fin n) (t : B)
open Classical
namespace Formalism.MainNotions.G.GLWeightTheory
theorem _root_.solution (v : ι × Fin n) :
    matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) (X v) =
      if v.1 ∈ S ∧ v = sourceVar LL a b v.1 then X v + C (letterSign B LL v.1 * t) * X (targetVar LL a b v.1) else X v := by
  obtain ⟨l, c⟩ := v
  rw [matrixSubst_X]
  simp only [Matrix.transvection, Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib,
    sum_C_one_col, sum_C_one_row, sum_C_single_col, sum_C_single_row, sourceVar, targetVar, letterSign]
  by_cases hS : l ∈ S <;> by_cases hv : LL.vec l <;> simp [hS, hv]
  all_goals split_ifs <;> simp
end Formalism.MainNotions.G.GLWeightTheory
