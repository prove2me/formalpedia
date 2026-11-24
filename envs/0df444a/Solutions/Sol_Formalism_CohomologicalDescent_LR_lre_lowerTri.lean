-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lre_lowerTri
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:29.609712+00:00
-- url     : https://prove2.me/submissions/11ea5fbb-a03b-40e5-a143-391eb12d10f9

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lre_le_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
open scoped MonomialOrder
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r)
    (hI : ∀ k, StrictMono (I k)) : LowerTri (bidetExp sz hsz I) := by
  intro a s has
  unfold bidetExp
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Finsupp.single_apply, if_neg]
  intro h
  have h1 : I k p = a := congrArg Prod.fst h
  have h2 : Fin.castLE (hsz k) p = s := congrArg Prod.snd h
  have h3 := lre_le_apply (I k) (hI k) p
  have h4 : p.val = s.val := by rw [← h2]; rfl
  rw [h1] at h3
  omega
end Formalism.CohomologicalDescent.LR
