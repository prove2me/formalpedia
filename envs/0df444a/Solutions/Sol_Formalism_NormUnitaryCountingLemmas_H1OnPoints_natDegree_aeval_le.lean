-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.H1OnPoints.natDegree_aeval_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:10:01.003699+00:00
-- url     : https://prove2.me/submissions/53647eea-ed30-49b3-841f-f3702ee69a76

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
theorem _root_.solution {B : Type*} [CommRing B] [Algebra R B] {N n : ℕ} {ν : Fin (N + 1) → ℕ}
    (F : MvPolynomial (Fin (N + 1) × Fin n) R) (hF : IsWeightedHomogeneous (blockWt (N + 1) n) F ν)
    (y : Fin (N + 1) × Fin n → Polynomial B)
    (hy : ∀ p, (y p).natDegree ≤ if p.1 = 0 then 1 else 0) : (aeval y F).natDegree ≤ ν 0 := by
  rw [F.as_sum, map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  have hw : Finsupp.weight (blockWt (N + 1) n) d = ν := hF (mem_support_iff.mp hd)
  rw [aeval_monomial, Polynomial.algebraMap_apply]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Finsupp.prod_fintype _ _ (by simp)]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ p, (y p ^ d p).natDegree ≤ ∑ p : Fin (N + 1) × Fin n, d p * (if p.1 = 0 then 1 else 0) :=
        Finset.sum_le_sum fun p _ => Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hy p))
    _ = ν 0 := by
        rw [← blockSum d hw 0, Fintype.sum_prod_type]
        simp
end Formalism.NormUnitaryCountingLemmas.H1OnPoints
