-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.supp_le_of_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:49:51.245714+00:00
-- url     : https://prove2.me/submissions/664d793c-d767-497b-b7f8-e83a18420f61

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjectionPos

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
theorem _root_.solution {σ : Type} (Q : Set (σ →₀ ℕ)) (S : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p]))
    (h : ∀ m ∈ Q, monomial m (1 : ℚ_[p]) ∈ S) : restrictSupport ℚ_[p] Q ≤ S := by
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx
  rw [x.as_sum]
  refine S.sum_mem fun m hm => ?_
  have hmon : monomial m (coeff m x) = coeff m x • monomial m (1 : ℚ_[p]) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmon]
  exact S.smul_mem _ (h m (hx hm))
end Formalism.InvariantFactorPaths.L4
