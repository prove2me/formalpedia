-- Prove2me | solution 1 for Formalism.G0.DetDividesP.aeval_weighted_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:22.627624+00:00
-- url     : https://prove2.me/submissions/cf81f9e9-7a34-4148-8a72-0072780e81c2

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Polynomial
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution {σ : Type} {B : Type} [CommSemiring B] [Algebra K B] (w : σ → ℕ)
    {φ : MvPolynomial σ K} {n : ℕ} (hφ : MvPolynomial.IsWeightedHomogeneous w φ n) (t : B) (z : σ → B) :
    MvPolynomial.aeval (fun p => t ^ (w p) * z p) φ = t ^ n * MvPolynomial.aeval z φ := by
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  have hw : Finsupp.weight w m = n := hφ (MvPolynomial.mem_support_iff.mp hm)
  have : (m.prod fun p k => (t ^ w p * z p) ^ k) = t ^ n * m.prod fun p k => z p ^ k := by
    simp only [mul_pow, Finsupp.prod_mul]
    congr 1
    rw [← hw, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, smul_eq_mul, mul_comm]
  rw [this]; ring
end Formalism.G0.DetDividesP
