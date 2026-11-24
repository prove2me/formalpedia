-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.transvectionExpansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:02:44.11981+00:00
-- url     : https://prove2.me/submissions/f24de090-21ea-422a-a405-702d7893090d

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_SumFinsuppAntidiagEqSumPiFinset
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_transvection_monomial
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_map_dividedPowerMonomial
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_dividedPower_monomial
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_C


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
namespace Formalism.MainNotions.G.GLWeightTheory
theorem _root_.solution : TransvectionExpansion := by
  unfold TransvectionExpansion
  intro R B _ _ ι _ LL n S φ a b _ t F N hF
  have key : ∀ v ∈ F.support,
      matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) (monomial v (coeff v F)) =
        ∑ k ∈ Finset.range N, C (t ^ k) * MvPolynomial.map φ (Formalism.MainNotions.G.divPow R LL S a b k (monomial v (coeff v F))) := by
    intro v hv
    have hv' : (v.sum fun _ e => e) < N := lt_of_le_of_lt (MvPolynomial.le_totalDegree hv) hF
    have hmono : (monomial v (coeff v F) : MvPolynomial (ι × Fin n) R) = C (coeff v F) * monomial v 1 := by
      rw [MvPolynomial.C_mul_monomial, mul_one]
    have hL : matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) (monomial v (coeff v F)) =
        C (φ (coeff v F)) * ∑ k ∈ Finset.range N, C (t ^ k) * Formalism.MainNotions.G.divPowMono B LL S a b k v := by
      rw [hmono, map_mul, matrixSubst_C, matrixSubst_transvection_monomial LL S a b t v φ N hv']
    rw [hL, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dividedPower_monomial, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_dividedPowerMonomial]
    ring
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  refine (Finset.sum_congr rfl key).trans ?_
  conv_rhs => rw [F.as_sum]
  simp only [map_sum, Finset.mul_sum]
  exact Finset.sum_comm
end Formalism.MainNotions.G.GLWeightTheory
