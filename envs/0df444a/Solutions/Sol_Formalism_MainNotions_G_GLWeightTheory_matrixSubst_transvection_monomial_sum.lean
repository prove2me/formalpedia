-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.matrixSubst_transvection_monomial_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:36:40.752981+00:00
-- url     : https://prove2.me/submissions/1a6cb6fe-9f28-41f1-9538-a4bdbed14dcc

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionX
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_transvection_monomial_prod
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_monomial_mul_prod_binomial_term

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
open Classical
namespace Formalism.MainNotions.G.GLWeightTheory
theorem _root_.solution :
    matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) (monomial m 1) =
      ∑ p ∈ Fintype.piFinset (fun l : ι => Finset.range (sourceExp LL S a b m l + 1)),
        C (t ^ (∑ l, p l)) * monomial (shiftedExponent LL a b m p) (rootShiftCoefficient B LL a b m p) := by
  rw [matrixSubst_transvection_monomial_prod]
  simp_rw [add_pow]
  rw [Finset.prod_univ_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  refine monomial_mul_prod_binomial_term LL S a b t m p fun l => ?_
  have hl := Fintype.mem_piFinset.1 hp l
  rw [Finset.mem_range] at hl
  omega
end Formalism.MainNotions.G.GLWeightTheory
