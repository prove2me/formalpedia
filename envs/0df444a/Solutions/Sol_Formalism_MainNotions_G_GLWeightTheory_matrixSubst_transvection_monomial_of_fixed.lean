-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.matrixSubst_transvection_monomial_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:12:41.970527+00:00
-- url     : https://prove2.me/submissions/02e905ce-e0dc-478e-a8ed-6b657ee669c1

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionX
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_transvection_X


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
theorem _root_.solution (m0 : ι × Fin n →₀ ℕ) (h0 : ∀ l ∈ S, m0 (sourceVar LL a b l) = 0) :
    matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) (monomial m0 1) = monomial m0 1 := by
  classical
  simp only [monomial_eq, map_one, one_mul, Finsupp.prod, map_prod, map_pow]
  refine Finset.prod_congr rfl fun v hv => ?_
  have hv' : ¬ (v.1 ∈ S ∧ v = sourceVar LL a b v.1) := by
    rintro ⟨hS, he⟩
    exact (Finsupp.mem_support_iff.1 hv) ((congrArg m0 he).trans (h0 _ hS))
  rw [matrixSubst_transvection_X, if_neg hv']
end Formalism.MainNotions.G.GLWeightTheory
