-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.pow_mul_eval_homogeneous_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:17:20.201887+00:00
-- url     : https://prove2.me/submissions/c62e0fff-035c-4205-b574-ac713d9ec75d

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {σ S : Type*} [CommRing S] (φ ψ : MvPolynomial σ ℤ →ₐ[ℤ] S) (d e : S)
    (h : ∀ v, d * φ (X v) = e * ψ (X v)) (N : ℕ) (x : MvPolynomial σ ℤ) (hx : x.IsHomogeneous N) :
    d ^ N * φ x = e ^ N * ψ x := by
  conv_lhs => rw [x.as_sum]
  conv_rhs => rw [x.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hN : ∑ v ∈ m.support, m v = N := by
    have := hx (mem_support_iff.mp hm)
    rw [Finsupp.weight_apply] at this
    simpa [Finsupp.sum] using this
  rw [monomial_eq, map_mul, map_mul, Finsupp.prod, map_prod, map_prod, ← hN, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_pow_eq_pow_sum, mul_left_comm, mul_left_comm _ (ψ _), ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib, algHom_C, algHom_C]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_pow, map_pow, ← mul_pow, ← mul_pow, h]
end Formalism.CohomologicalDescent.LD
