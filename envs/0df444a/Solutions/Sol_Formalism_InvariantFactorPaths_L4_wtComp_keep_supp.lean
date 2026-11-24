-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.wtComp_keep_supp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:48.341114+00:00
-- url     : https://prove2.me/submissions/9a3594d7-9af3-457b-8ecb-7f12efe5fde8

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (w : Fin r → ℤ) (Q : Set (Fin N × Fin r →₀ ℕ)) :
    ∀ x ∈ restrictSupport ℚ_[p] Q, wtComp p LL j w x ∈ restrictSupport ℚ_[p] Q := by
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx
  unfold wtComp compP
  refine Submodule.sum_mem _ fun m hm => ?_
  split_ifs
  · rw [MvPolynomial.mem_restrictSupport_iff]
    intro m' hm'
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm')]
    exact hx (Finset.mem_coe.mpr hm)
  · exact Submodule.zero_mem _
end Formalism.InvariantFactorPaths.L4
