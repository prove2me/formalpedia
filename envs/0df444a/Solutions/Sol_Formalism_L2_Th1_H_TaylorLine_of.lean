-- Prove2me | solution 1 for Formalism.L2.Th1.H.TaylorLine_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:42:45.475422+00:00
-- url     : https://prove2.me/submissions/6d2017b2-9ebe-4d38-9e55-1493e71697e7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_IteratedDerivLine
import Theorems.Thm_Formalism_L2_Th1_H_cntVec_sum
import Theorems.Thm_Formalism_L2_Th1_H_cntVec_prod
import Theorems.Thm_Formalism_L2_Th1_H_taylorMv_coeff
import Theorems.Thm_Formalism_L2_Th1_H_multilinear_diag
import Theorems.Thm_Formalism_L2_Th1_H_iteratedDeriv_line

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
theorem _root_.solution (h : LineCoeff) : TaylorLine := by
  intro n _ _ F hF v
  ext k
  rw [h ℂ n v (taylorMv F) k, Formalism.L2.Th1.F.taylor0, PowerSeries.coeff_mk, iteratedDeriv_line F hF v k,
    multilinear_diag]
  have h1 : ∀ ν ∈ Finset.finsuppAntidiag (Finset.univ : Finset n) k,
      MvPowerSeries.coeff ν (taylorMv F) * ∏ i, v i ^ ν i
      = ((k.factorial : ℕ) : ℂ)⁻¹ * ∑ f : Fin k → n with cntVec f = ν,
          (∏ j, v (f j)) * iteratedFDeriv ℂ k F 0 fun j => Pi.single (f j) (1 : ℂ) := by
    intro ν hν
    rw [Finset.mem_finsuppAntidiag] at hν
    rw [taylorMv_coeff F k ν (by rw [Finsupp.degree_eq_sum]; exact hν.1), mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [← (Finset.mem_filter.1 hf).2, cntVec_prod, mul_comm]
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum,
    Finset.sum_fiberwise_of_maps_to (fun f _ => by simp [Finset.mem_finsuppAntidiag, cntVec_sum]),
    div_eq_inv_mul]
end Formalism.L2.Th1.H
