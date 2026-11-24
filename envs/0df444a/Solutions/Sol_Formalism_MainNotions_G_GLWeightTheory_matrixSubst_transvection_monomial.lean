-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.matrixSubst_transvection_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:47:42.132204+00:00
-- url     : https://prove2.me/submissions/43bcce10-36c1-4f7e-834c-e1c90d0a50bb

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_SumFinsuppAntidiagEqSumPiFinset
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_dividedPowerMonomial_eq_sum
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sum_finsuppAntidiag_eq_sum_piFinset
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sum_sourceExp_le
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_transvection_monomial_sum


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
theorem _root_.solution (N : ℕ) (hN : (m.sum fun _ e => e) < N) :
    matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) (monomial m 1) =
      ∑ k ∈ Finset.range N, C (t ^ k) * divPowMono B LL S a b k m := by
  classical
  rw [matrixSubst_transvection_monomial_sum]
  have hmaps : ∀ p ∈ Fintype.piFinset (fun l : ι => Finset.range (sourceExp LL S a b m l + 1)),
      (∑ l, p l) ∈ Finset.range N := by
    intro p hp
    rw [Fintype.mem_piFinset] at hp
    rw [Finset.mem_range]
    calc ∑ l, p l ≤ ∑ l, sourceExp LL S a b m l :=
          Finset.sum_le_sum fun l _ => by have := Finset.mem_range.mp (hp l); omega
      _ ≤ _ := sum_sourceExp_le LL S a b m
      _ < N := hN
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dividedPowerMonomial_eq_sum, sum_finsuppAntidiag_eq_sum_piFinset, Finset.mul_sum]
  refine Finset.sum_congr (by ext p; simp only [Finset.mem_filter]) fun p hp => ?_
  have hk : ∑ l, p l = k := (Finset.mem_filter.mp hp).2
  rw [hk]
end Formalism.MainNotions.G.GLWeightTheory
