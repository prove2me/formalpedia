-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.map_dividedPowerMonomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:40:13.855108+00:00
-- url     : https://prove2.me/submissions/1abcc05d-3ffc-4438-bc00-a103db32b5a6

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_SumFinsuppAntidiagEqSumPiFinset

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
theorem _root_.solution (k : ℕ) :
    MvPolynomial.map φ (divPowMono R LL S a b k m) = divPowMono B LL S a b k m := by
  unfold Formalism.MainNotions.G.divPowMono
  rw [map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  have h : ∀ l, φ (if LL.vec l then ((m (l, b)).choose (f l) : R) else (-1 : R) ^ (f l) * ((m (l, a)).choose (f l) : R)) =
      (if LL.vec l then ((m (l, b)).choose (f l) : B) else (-1 : B) ^ (f l) * ((m (l, a)).choose (f l) : B)) :=
    fun l => by split_ifs <;> simp
  simp only [MvPolynomial.map_monomial, map_prod, h]
end Formalism.MainNotions.G.GLWeightTheory
