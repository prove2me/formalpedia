-- Prove2me | solution 1 for EdenVerified.D04_polynomial_field
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:01:37.479494+00:00
-- url     : https://prove2.me/submissions/b8eb6b2c-fc00-4506-802b-cd5f3efc4913

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_contDiff_vectorField
import Theorems.Thm_Eden_eval_vectorFieldPolynomial
import Theorems.Thm_Eden_totalDegree_vectorFieldPolynomial_first
import Theorems.Thm_Eden_totalDegree_vectorFieldPolynomial_le
import Theorems.Thm_Eden_vectorFieldPolynomial_degree


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) :
    (∀ p : PhaseSpace, vectorField c p =
      !₂[q (radiusSq₁ p) * p 0 - p 1, q (radiusSq₁ p) * p 1 + p 0,
        q (radiusSq₂ p) * p 2 - Real.sqrt 2 * p 3,
        q (radiusSq₂ p) * p 3 + Real.sqrt 2 * p 2, -c * p 4]) ∧
    (∀ (p : PhaseSpace) (i : Fin 5),
      MvPolynomial.eval p (vectorFieldPolynomial c i) = vectorField c p i) ∧
    (∀ i : Fin 5, (vectorFieldPolynomial c i).totalDegree ≤ 5) ∧
    (vectorFieldPolynomial c 0).totalDegree = 5 ∧
    Finset.univ.sup (fun i => (vectorFieldPolynomial c i).totalDegree) = 5 ∧
    (∀ n : WithTop ℕ∞, ContDiff ℝ n (vectorField c)) :=
  ⟨fun _ => rfl, eval_vectorFieldPolynomial c, totalDegree_vectorFieldPolynomial_le c,
    totalDegree_vectorFieldPolynomial_first c, vectorFieldPolynomial_degree c,
    contDiff_vectorField c⟩
end EdenVerified
