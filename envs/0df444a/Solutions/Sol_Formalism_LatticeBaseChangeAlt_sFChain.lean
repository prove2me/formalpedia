-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.sFChain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:15:36.935776+00:00
-- url     : https://prove2.me/submissions/4c5de15b-3479-48e6-a441-8801d52f8c03

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
theorem _root_.solution : SFChain := by
  intro ξn lam d' ρ φ t p RR T c hξ hl hd hρ hφ hφ2 ht hRR hTc hc1
  have h1 : ξn ^ 2 * lam ^ 2 ≤ d' ^ 2 := by
    have : 0 ≤ ξn * lam := by positivity
    nlinarith
  have hξ2 : 0 < ξn ^ 2 := by positivity

  have h2 : 2 * (RR * (T * c)) * (d' ^ 2 * ρ) < ξn ^ 2 * p := by nlinarith
  have h3 : T * c ≤ RR * (T * c) := by nlinarith
  have h4 : (T * c) * (ξn ^ 2 * lam ^ 2 * ρ) ≤ (RR * (T * c)) * (d' ^ 2 * ρ) := by
    apply mul_le_mul h3 (mul_le_mul_of_nonneg_right h1 hρ) (by positivity) (by nlinarith)
  have h5 : (T * c) * (ξn ^ 2 * φ) ≤ (T * c) * (ξn ^ 2 * (2 * ρ * lam ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hφ2 hξ2.le) hTc
  have h6 : ξn ^ 2 * (T * c * φ) < ξn ^ 2 * p := by nlinarith
  exact lt_of_mul_lt_mul_left h6 hξ2.le
end Formalism.LatticeBaseChangeAlt
