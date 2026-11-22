-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.vchoose_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:25:20.875805+00:00
-- url     : https://prove2.me/submissions/15db8a65-a75b-4d22-8dfa-73e5ab20a5b2

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution {t k T B : ℕ} (ht : t ≤ T) (hB : Nat.log p T ≤ B) :
    padicValNat p (t.choose k) ≤ B := by
  rw [← Nat.factorization_def _ hp.out]
  exact Nat.factorization_choose_le_log.trans ((Nat.log_mono_right ht).trans hB)
end Formalism.GM.gammaIntegralityLemmas
