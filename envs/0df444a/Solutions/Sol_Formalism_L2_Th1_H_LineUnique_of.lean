-- Prove2me | solution 1 for Formalism.L2.Th1.H.LineUnique_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:26:18.111129+00:00
-- url     : https://prove2.me/submissions/ebfe5b31-562d-459a-825a-82b3792b659e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_IteratedDerivLine
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution (h : LineCoeff) : LineUnique := by
  classical
  intro K _ _ n _ T T' hv
  ext ν
  set k := ∑ i, ν i with hk
  let p : MvPolynomial n K := ∑ μ ∈ Finset.finsuppAntidiag Finset.univ k,
    MvPolynomial.monomial μ (MvPowerSeries.coeff μ T)
  let q : MvPolynomial n K := ∑ μ ∈ Finset.finsuppAntidiag Finset.univ k,
    MvPolynomial.monomial μ (MvPowerSeries.coeff μ T')
  have hpq : p = q := by
    refine MvPolynomial.funext fun v => ?_
    have h1 := h K n v T k
    have h2 := h K n v T' k
    rw [hv v, h2] at h1
    simp only [p, q, map_sum, MvPolynomial.eval_monomial]
    simp only [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    exact h1.symm
  have hν : ν ∈ Finset.finsuppAntidiag Finset.univ k := by simp [Finset.mem_finsuppAntidiag, hk]
  have hc : ∀ S : MvPowerSeries n K, MvPolynomial.coeff ν (∑ μ ∈ Finset.finsuppAntidiag Finset.univ k,
      MvPolynomial.monomial μ (MvPowerSeries.coeff μ S)) = MvPowerSeries.coeff ν S := by
    intro S
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' _ ν, if_pos hν]
  rw [← hc T, ← hc T']
  exact congrArg _ hpq
end Formalism.L2.Th1.H
