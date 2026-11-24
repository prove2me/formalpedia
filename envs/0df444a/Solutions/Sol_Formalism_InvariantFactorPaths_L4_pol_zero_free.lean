-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.pol_zero_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:49:49.242389+00:00
-- url     : https://prove2.me/submissions/ff68579d-db84-43b2-b17b-220f748c74e3

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters (K + 1)) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hx : x ∈ Pol p r (setLast LL 0)) : x ∈ FreeLast p K r := by
  rw [Pol, mem_restrictSupport_iff] at hx
  rw [FreeLast, mem_restrictSupport_iff]
  intro m hm c
  have h1 : ∑ c, m (Fin.last K, c) = (setLast LL 0).deg (Fin.last K) := hx hm (Fin.last K)
  have h2 : (setLast LL 0).deg (Fin.last K) = 0 := by simp [setLast]
  rw [h2] at h1
  exact Finset.sum_eq_zero_iff.mp h1 c (Finset.mem_univ c)
end Formalism.InvariantFactorPaths.L4
