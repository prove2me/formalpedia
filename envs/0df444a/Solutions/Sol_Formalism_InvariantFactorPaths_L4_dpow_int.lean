-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.dpow_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:15:42.724219+00:00
-- url     : https://prove2.me/submissions/a6304301-fb2e-419f-b615-eb8c214e4a65

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_dpow_int_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (c : Fin r) (hc : c ≠ 0) (k : ℕ) (h : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hh : h ∈ IntPol p (Fin N × Fin r)) : dpow p LL j c k h ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨P, rfl⟩ := LinearMap.mem_range.mp hh
  exact dpow_int_map p LL j c hc P k
end Formalism.InvariantFactorPaths.L4
