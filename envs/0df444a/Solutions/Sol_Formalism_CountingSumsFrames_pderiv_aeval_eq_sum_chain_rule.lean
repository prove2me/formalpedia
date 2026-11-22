-- Prove2me | solution 1 for Formalism.CountingSumsFrames.pderiv_aeval_eq_sum_chain_rule
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:09.215888+00:00
-- url     : https://prove2.me/submissions/7efa5f1e-e19e-4e22-9a99-b4211ade10be

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice

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
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution {σ : Type} [Fintype σ] (u : σ → MvPolynomial σ K) (v : σ) (f : MvPolynomial σ K) :
    pderiv v (aeval u f) = ∑ w : σ, aeval u (pderiv w f) * pderiv v (u w) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hp, map_add, pderiv_X, add_mul,
      Finset.sum_add_distrib]
    have h1 : ∑ w : σ, aeval u p * aeval u ((Pi.single w 1 : σ → MvPolynomial σ K) n) * pderiv v (u w) =
        aeval u p * pderiv v (u n) := by
      rw [Finset.sum_eq_single n]
      · simp
      · intro b _ hb
        simp [hb.symm]
      · intro h; exact absurd (Finset.mem_univ n) h
    rw [h1, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    ring
end Formalism.CountingSumsFrames
