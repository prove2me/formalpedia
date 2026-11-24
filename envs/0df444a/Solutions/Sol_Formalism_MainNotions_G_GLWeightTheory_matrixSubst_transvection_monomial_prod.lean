-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.matrixSubst_transvection_monomial_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:29:56.261951+00:00
-- url     : https://prove2.me/submissions/2ec6b155-b967-423a-bc6d-a1c5e75c4d9d

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionX
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_prod_monomial_eq_monomial_sum_prod
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sourcePart_le
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sub_sourcePart_sourceVar
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_transvection_monomial_of_fixed
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_transvection_X
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sourceVar_fst


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
variable {B : Type*} [CommRing B] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
  (a b : Fin n) (t : B) (m : ι × Fin n →₀ ℕ)
variable {R : Type*} [CommRing R] (φ : R →+* B)
namespace Formalism.MainNotions.G.GLWeightTheory
theorem _root_.solution :
    matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) (monomial m 1) =
      monomial (m - sourceVariableExponent LL S a b m) 1 *
        ∏ l : ι, (C (letterSign B LL l * t) * X (targetVar LL a b l) + X (sourceVar LL a b l)) ^ (sourceExp LL S a b m l) := by
  classical
  have hsplit : (monomial m (1 : R) : MvPolynomial (ι × Fin n) R) =
      monomial (m - sourceVariableExponent LL S a b m) 1 * monomial (sourceVariableExponent LL S a b m) 1 := by
    rw [monomial_mul, one_mul, tsub_add_cancel_of_le (sourcePart_le LL S a b m)]
  have hprod : (monomial (sourceVariableExponent LL S a b m) (1 : R) : MvPolynomial (ι × Fin n) R) =
      ∏ l : ι, X (sourceVar LL a b l) ^ sourceExp LL S a b m l := by
    unfold sourceVariableExponent
    simp only [X_pow_eq_monomial]
    rw [prod_monomial_eq_monomial_sum_prod, Finset.prod_const_one]
  rw [hsplit, map_mul, matrixSubst_transvection_monomial_of_fixed (LL := LL) (S := S) (a := a) (b := b) (t := t)
    (φ := φ) (m0 := m - sourceVariableExponent LL S a b m) (h0 := sub_sourcePart_sourceVar LL S a b m)]
  congr 1
  rw [hprod, map_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [map_pow]
  by_cases hl : l ∈ S
  · rw [matrixSubst_transvection_X, sourceVar_fst, if_pos ⟨hl, rfl⟩, add_comm]
  · have he : sourceExp LL S a b m l = 0 := by
      unfold sourceExp
      rw [if_neg hl]
    rw [he, pow_zero, pow_zero]
end Formalism.MainNotions.G.GLWeightTheory
