-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lcassem_sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:30:22.234746+00:00
-- url     : https://prove2.me/submissions/2a6d08cc-211e-408b-9993-4f85b745372b

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCassemLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.GradedWeylDivisibility
open scoped MonomialOrder
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {σ R : Type*} [CommRing R] (o : MonomialOrder σ) {f g : MvPolynomial σ R}
    (hdeg : o.degree g = o.degree f) (hlc : o.leadingCoeff g = 1)
    (hne : f - o.leadingCoeff f • g ≠ 0) :
    o.degree (f - o.leadingCoeff f • g) ≺[o] o.degree f := by
  have hle : o.toSyn (o.degree (f - o.leadingCoeff f • g)) ≤ o.toSyn (o.degree f) := by
    refine (MonomialOrder.degree_sub_le (m := o)).trans (sup_le le_rfl ?_)
    rw [← hdeg]
    exact MonomialOrder.degree_smul_le (m := o)
  refine lt_of_le_of_ne hle fun heq => hne ?_

  have hd : o.degree (f - o.leadingCoeff f • g) = o.degree f := o.toSyn.injective heq
  have h1 : f.coeff (o.degree f) = o.leadingCoeff f := rfl
  have h2 : g.coeff (o.degree f) = 1 := by rw [← hdeg]; exact hlc
  rw [← o.coeff_degree_eq_zero_iff, hd, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, h1, h2,
    smul_eq_mul, mul_one, sub_self]
end Formalism.GradedWeylDivisibility
