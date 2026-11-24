-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.H1OnPoints.aeval_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:09:59.568919+00:00
-- url     : https://prove2.me/submissions/11946b30-d82b-41a8-bb6c-d00a2f900f99

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NatDegreeAevalLe
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_H1OnPoints_blockSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.H1OnPoints
variable {R : Type*} [CommRing R]
namespace Formalism.NormUnitaryCountingLemmas.H1OnPoints
theorem _root_.solution {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} {ν : Fin N → ℕ}
    (F : MvPolynomial (Fin N × Fin n) R)
    (hF : IsWeightedHomogeneous (blockWt N n) F ν) (lam : Fin N → S) (y : Fin N × Fin n → S) :
    aeval (fun p => lam p.1 * y p) F = (∏ j, lam j ^ ν j) * aeval y F := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  simp only [map_sum, Finset.mul_sum, aeval_monomial]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight (blockWt N n) d = ν := hF (mem_support_iff.mp hd)
  have hprod : (d.prod fun p k => lam p.1 ^ k) = ∏ j, lam j ^ ν j := by
    rw [Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun j _ => ?_
    show ∏ k, lam j ^ d (j, k) = _
    rw [Finset.prod_pow_eq_pow_sum, blockSum d hw j]
  have : (d.prod fun p k => (lam p.1 * y p) ^ k) =
      (d.prod fun p k => lam p.1 ^ k) * d.prod fun p k => y p ^ k := by
    rw [← Finsupp.prod_mul]
    simp [mul_pow]
  rw [this, hprod]
  ring
end Formalism.NormUnitaryCountingLemmas.H1OnPoints
