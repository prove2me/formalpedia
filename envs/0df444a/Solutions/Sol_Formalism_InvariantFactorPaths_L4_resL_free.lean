-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.resL_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:35:47.380351+00:00
-- url     : https://prove2.me/submissions/dcc8d341-56d3-4089-9549-e3770d38fbbf

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
theorem _root_.solution (v : σ) (x : MvPolynomial σ ℚ_[p]) : resL p v 0 x ∈ FreeOf p v := by
  rw [FreeOf, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  rw [Finset.mem_coe, MvPolynomial.mem_support_iff] at hm
  change (initPart v 0 x).coeff m ≠ 0 at hm
  rw [coeff_initPart] at hm
  split_ifs at hm with h
  · exact h
  · exact absurd rfl hm
end Formalism.InvariantFactorPaths.L4
