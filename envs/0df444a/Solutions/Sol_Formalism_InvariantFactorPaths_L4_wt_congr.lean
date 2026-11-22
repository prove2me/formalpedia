-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.wt_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:37:18.252067+00:00
-- url     : https://prove2.me/submissions/7aa4af07-0634-4124-bf0a-42e683c62c9a

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
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
theorem _root_.solution {N : ℕ} (LL : Letters N) (j : ℕ) (c : Fin r) (m m' : Fin N × Fin r →₀ ℕ)
    (h : ∀ i : Fin N, (i : ℕ) < j → m (i, c) = m' (i, c)) : wt LL j c m = wt LL j c m' := by
  simp only [wt]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : (i : ℕ) < j
  · simp [h1, h i h1]
  · simp [h1]
end Formalism.InvariantFactorPaths.L4
