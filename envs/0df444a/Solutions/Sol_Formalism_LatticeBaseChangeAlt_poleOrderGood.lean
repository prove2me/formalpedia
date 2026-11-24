-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.poleOrderGood
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:35:29.500706+00:00
-- url     : https://prove2.me/submissions/e55f2ed7-6098-403c-93f3-5eadb7a3a095

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FilIntegerStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LatticeBaseChangeAlt
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : PoleOrderGood := by
  intro ep T ν νs c' vet e hep hc hv hν ⟨n, hn⟩ he
  have hepR : (1 : ℝ) ≤ ep := by exact_mod_cast hep
  have hT0 : (0 : ℝ) ≤ T := by positivity
  have hy : 0 ≤ (ep : ℝ) * (T * c' * vet) := by positivity
  rw [div_le_iff₀ (by linarith)]
  have hint : (ep : ℝ) * ((T : ℝ) * ν - e) = (((T : ℤ) * n - ep * e : ℤ) : ℝ) := by
    push_cast; rw [← hn]; ring
  rw [hint, Int.ceil_intCast, Int.cast_max]
  apply max_le
  · simpa [mul_comm] using hy
  · rw [← hint]
    have : (T : ℝ) * ν - e ≤ T * c' * vet := by nlinarith
    nlinarith
end Formalism.LatticeBaseChangeAlt
