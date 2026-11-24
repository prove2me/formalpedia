-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.pderiv_freeOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:49:52.431115+00:00
-- url     : https://prove2.me/submissions/1091b93f-c837-49af-b8b0-6fac5473b928

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds

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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution {σ : Type} (u v : σ) (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ FreeOf p v) :
    pderiv u x ∈ FreeOf p v := by
  classical
  rw [FreeOf, mem_restrictSupport_iff] at hx ⊢
  intro m hm
  rw [Finset.mem_coe, mem_support_iff, coeff_pderiv] at hm
  have h1 : m + Finsupp.single u 1 ∈ x.support := mem_support_iff.mpr (left_ne_zero_of_mul hm)
  have h2 : (m + Finsupp.single u 1 : σ →₀ ℕ) v = 0 := hx (Finset.mem_coe.mpr h1)
  rw [Finsupp.add_apply] at h2
  exact (Nat.add_eq_zero_iff.mp h2).1
end Formalism.InvariantFactorPaths.L4
