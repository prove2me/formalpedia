-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.wtComp_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:44:26.142893+00:00
-- url     : https://prove2.me/submissions/da00693b-2ce1-4ac6-996d-ee2412087a14

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
theorem _root_.solution (LL : Letters N) (j : ℕ) (w : Fin r → ℤ) :
    ∀ x ∈ WtSpC p LL j univ w, wtComp p LL j w x = x := by
  intro x hx
  rw [WtSpC, MvPolynomial.mem_restrictSupport_iff] at hx
  unfold wtComp compP
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff x]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : ∀ c ∈ univ, wt LL j c m = w c := hx (Finset.mem_coe.mpr hm)
  split_ifs with h
  · rfl
  · exact absurd (fun c => hm' c (Finset.mem_univ c)) h
end Formalism.InvariantFactorPaths.L4
