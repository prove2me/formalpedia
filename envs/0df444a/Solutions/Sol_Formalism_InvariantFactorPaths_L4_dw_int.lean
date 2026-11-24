-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.dw_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:23:10.697937+00:00
-- url     : https://prove2.me/submissions/d042df5e-b025-48bf-8d43-de8922af97a2

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_dpow_int
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_dw_cons

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
variable (M : WithTop ℤ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (l : List (Fin r × ℕ)) (hl : ∀ ck ∈ l, ck.1 ≠ 0) (b : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hb : b ∈ IntPol p (Fin N × Fin r)) : dw p LL j l b ∈ IntPol p (Fin N × Fin r) := by
  induction l with
  | nil => exact hb
  | cons ck l ih =>
    rw [dw_cons]
    exact dpow_int p LL j _ (hl ck List.mem_cons_self) _ _ (ih fun a ha => hl a (List.mem_cons_of_mem _ ha))
end Formalism.InvariantFactorPaths.L4
