-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.frob_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:34:23.71395+00:00
-- url     : https://prove2.me/submissions/580109eb-9116-4c2a-96fe-7ada642bc674

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
variable {k : Type*} [Field k] {Z : Type*} {v : AddValuation k (WithTop ℝ)}
  {r w w' w1 w2 wa wb a₀ : ℝ} {f g a b : MvPowerSeries Z k}
namespace Formalism.BaseCaseIdentities
theorem _root_.solution {N : ℕ} (hN : 1 ≤ N) : frob N (0 : MvPowerSeries Z k) = 0 := by
  ext B
  by_cases h : ∀ d, N ∣ B d
  · rw [coeff_frob_of_dvd h]; simp; omega
  · rw [coeff_frob_of_not_dvd h]; simp
end Formalism.BaseCaseIdentities
