-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.resL_keep_supp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:33:39.675734+00:00
-- url     : https://prove2.me/submissions/1c03a67e-937e-4165-b3b3-4e8e77c36029

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto

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
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (v : σ) (e : ℕ) (Q : Set (σ →₀ ℕ)) :
    ∀ x ∈ restrictSupport ℚ_[p] Q, resL p v e x ∈ restrictSupport ℚ_[p] Q := by
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx ⊢
  intro m hm
  apply hx
  rw [Finset.mem_coe, MvPolynomial.mem_support_iff] at hm ⊢
  change (initPart v e x).coeff m ≠ 0 at hm
  rw [coeff_initPart] at hm
  split_ifs at hm with h
  · exact hm
  · exact absurd rfl hm
end Formalism.InvariantFactorPaths.L4
