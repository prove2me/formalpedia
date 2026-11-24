-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.wt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:35:49.833867+00:00
-- url     : https://prove2.me/submissions/d2ec7bfa-450a-48e6-ab74-dde173cf17b6

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RandomSubsetLemmaCounterexample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
open Finset
namespace Formalism.RankGapBounds.LocalQuadraticParts
theorem _root_.solution {α : Type*} [Fintype α] {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (T : Finset α) :
    0 ≤ wt δ T :=
  mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)
end Formalism.RankGapBounds.LocalQuadraticParts
