-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.wtComp_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:54.502803+00:00
-- url     : https://prove2.me/submissions/ddfc47a8-db43-4006-b495-823edd18679c

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (w : Fin r → ℤ) :
    ∀ x ∈ IntPol p (Fin N × Fin r), wtComp p LL j w x ∈ IntPol p (Fin N × Fin r) := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  unfold wtComp compP
  refine Submodule.sum_mem _ fun m _ => ?_
  split_ifs
  · exact ⟨monomial m (coeff m y), by simp [MvPolynomial.coeff_map]⟩
  · exact Submodule.zero_mem _
end Formalism.InvariantFactorPaths.L4
