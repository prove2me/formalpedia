-- Prove2me | solution 1 for Formalism.E.fischerInnerConjSymm_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:06.394248+00:00
-- url     : https://prove2.me/submissions/5aa25d02-c604-4a9b-a763-c170132993cb

import Definitions.Def_Formalism_FockGram_StatementFock
import Definitions.Def_Formalism_FockGram_FockGramProofs_FockHerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.E
namespace Formalism.E
theorem _root_.solution : FockHerm := by
  intro R τ _ _ f g
  classical
  unfold Formalism.E.fock
  rw [star_sum]
  have hf : ∀ m ∉ f.support, f.coeff m = 0 := fun m h => by simpa using h
  have hg : ∀ m ∉ g.support, g.coeff m = 0 := fun m h => by simpa using h
  have e1 : ∑ m ∈ f.support, star (f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R)) =
      ∑ m ∈ f.support ∪ g.support, star (f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R)) :=
    Finset.sum_subset Finset.subset_union_left (fun m _ hm => by simp [hf m hm])
  have e2 : ∑ m ∈ g.support, g.coeff m * star (f.coeff m) * (Formalism.A.mfact m : R) =
      ∑ m ∈ f.support ∪ g.support, g.coeff m * star (f.coeff m) * (Formalism.A.mfact m : R) :=
    Finset.sum_subset Finset.subset_union_right (fun m _ hm => by simp [hg m hm])
  rw [e1, e2]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [star_mul, mul_comm, mul_left_comm]
end Formalism.E
