-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.dividedPower_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:40:12.441272+00:00
-- url     : https://prove2.me/submissions/c508c429-e695-45b0-98c7-392780d14008

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
theorem _root_.solution (k : ℕ) (c : R) :
    divPow R LL S a b k (monomial m c) = c • divPowMono R LL S a b k m := by
  have h1 : (monomial m c : MvPolynomial (ι × Fin n) R) = c • MvPolynomial.basisMonomials (ι × Fin n) R m := by
    simp only [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [h1, map_smul]
  unfold Formalism.MainNotions.G.divPow
  rw [Module.Basis.constr_basis]
end Formalism.MainNotions.G.GLWeightTheory
