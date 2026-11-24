-- Prove2me | solution 1 for Formalism.CohomologicalDescent.label_vl_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:53.777131+00:00
-- url     : https://prove2.me/submissions/7b74e018-3da5-460a-9cee-0be7a92497f5

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
open Classical
namespace Formalism.CohomologicalDescent
theorem _root_.solution {l : ℕ} (_hl : l.Prime) {n : ℤ} (h0 : 0 < n) (h1 : n < (l : ℤ) ^ 2) :
    vl l n ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hdvd : (l : ℤ) ^ 2 ∣ n := by
    have h2 : (l : ℤ) ^ 2 ∣ (l : ℤ) ^ vl l n := pow_dvd_pow _ (by omega)
    refine h2.trans ?_
    have h3 : l ^ padicValNat l n.natAbs ∣ n.natAbs := pow_padicValNat_dvd
    have h4 : ((l ^ padicValNat l n.natAbs : ℕ) : ℤ) ∣ ((n.natAbs : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr h3
    rw [Int.natAbs_of_nonneg h0.le] at h4
    simpa [vl, padicValInt] using h4
  have := Int.le_of_dvd h0 hdvd
  linarith
end Formalism.CohomologicalDescent
