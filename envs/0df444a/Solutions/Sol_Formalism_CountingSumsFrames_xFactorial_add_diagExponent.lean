-- Prove2me | solution 1 for Formalism.CountingSumsFrames.xFactorial_add_diagExponent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:30.611902+00:00
-- url     : https://prove2.me/submissions/d4256d23-6549-418f-9535-6441c33867d6

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_diagExponent_inl
import Theorems.Thm_Formalism_CountingSumsFrames_factorial_add_eq_descFactorial_mul

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
theorem _root_.solution (m : XY k →₀ ℕ) (i : Fin k) (n : ℕ) :
    xFact (m + h3s i n) = (m (Sum.inl i) + n).descFactorial n * xFact m := by
  classical
  unfold xFact
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i), ← Finset.mul_prod_erase univ (fun j => (m (Sum.inl j)).factorial) (Finset.mem_univ i)]
  have h1 : ∏ j ∈ univ.erase i, ((m + h3s i n) (Sum.inl j)).factorial =
      ∏ j ∈ univ.erase i, (m (Sum.inl j)).factorial := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    simp [diagExponent_inl, this]
  rw [h1]
  simp only [Finsupp.add_apply, diagExponent_inl, if_true]
  rw [factorial_add_eq_descFactorial_mul, mul_assoc]
end Formalism.CountingSumsFrames
