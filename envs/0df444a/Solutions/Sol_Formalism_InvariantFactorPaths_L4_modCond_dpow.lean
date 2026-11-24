-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.modCond_dpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:15.37542+00:00
-- url     : https://prove2.me/submissions/5b6cbd44-273e-4279-90ce-9198f4e3c757

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_dw_snoc

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
theorem _root_.solution (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hh : ModCond p LL j M h) (c : Fin r) (hc : c ≠ 0)
    (k : ℕ) : ModCond p LL j M (dpow p LL j c k h) := by
  intro l hl m hm
  have := hh (l ++ [(c, k)]) (by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hl a ha
    · rw [List.mem_singleton.mp ha]; exact hc) m hm
  have e := dw_snoc p LL j (c, k) l h
  rw [e] at this
  exact this
end Formalism.InvariantFactorPaths.L4
