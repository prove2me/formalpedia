-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lcdeg_degreeOf_aeval_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:58.914022+00:00
-- url     : https://prove2.me/submissions/68d39c4d-ebda-4e42-be11-3b76ad3f5aaf

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCdegLemmas

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
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {σ τ R : Type*} [CommRing R] (f : σ → MvPolynomial τ R)
    (p : MvPolynomial σ R) (c : τ) (d : ℕ)
    (h : ∀ m ∈ p.support, ∑ v ∈ m.support, m v * degreeOf c (f v) ≤ d) :
    degreeOf c (aeval f p) ≤ d := by
  classical
  rw [aeval_def, eval₂_eq]
  have key : ∀ m ∈ p.support, degreeOf c (algebraMap R (MvPolynomial τ R) (coeff m p) *
      ∏ v ∈ m.support, f v ^ m v) ≤ d := by
    intro m hm
    rw [algebraMap_eq]
    refine (degreeOf_C_mul_le _ _ _).trans ?_
    exact (degreeOf_prod_le _ _ _).trans
      ((Finset.sum_le_sum fun v _ => degreeOf_pow_le _ _ _).trans (h m hm))
  clear h
  generalize p.support = s at key ⊢
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (degreeOf_add_le _ _ _).trans (max_le (key a (Finset.mem_insert_self _ _))
      (ih fun m hm => key m (Finset.mem_insert_of_mem hm)))
end Formalism.GradedWeylDivisibility
